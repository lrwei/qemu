/*
 * Tiny Code Generator for QEMU
 *
 * Copyright (c) 2008 Fabrice Bellard
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

#include "qemu/osdep.h"

/* Define to jump the ELF file used to communicate with GDB.  */
#undef DEBUG_JIT

#include "qemu/error-report.h"
#include "qemu/cutils.h"
#include "qemu/host-utils.h"
#include "qemu/qemu-print.h"
#include "qemu/timer.h"

/* Note: the long term plan is to reduce the dependencies on the QEMU
   CPU definitions. Currently they are used for qemu_ld/st
   instructions */
#define NO_CPU_IO_DEFS
#include "cpu.h"

#include "exec/exec-all.h"

#if !defined(CONFIG_USER_ONLY)
#include "hw/boards.h"
#endif

#include "tcg/tcg-op.h"
#include "exec/gen-icount.h"

#if UINTPTR_MAX == UINT32_MAX
# define ELF_CLASS  ELFCLASS32
#else
# define ELF_CLASS  ELFCLASS64
#endif
#ifdef HOST_WORDS_BIGENDIAN
# define ELF_DATA   ELFDATA2MSB
#else
# define ELF_DATA   ELFDATA2LSB
#endif

#include "elf.h"
#include "exec/log.h"
#include "sysemu/sysemu.h"

/* The CIE and FDE header definitions will be common to all hosts.  */
typedef struct {
    uint32_t len __attribute__((aligned((sizeof(void *)))));
    uint32_t id;
    uint8_t version;
    char augmentation[1];
    uint8_t code_align;
    uint8_t data_align;
    uint8_t return_column;
} DebugFrameCIE;

typedef struct QEMU_PACKED {
    uint32_t len __attribute__((aligned((sizeof(void *)))));
    uint32_t cie_offset;
    uintptr_t func_start;
    uintptr_t func_len;
} DebugFrameFDEHeader;

typedef struct QEMU_PACKED {
    DebugFrameCIE cie;
    DebugFrameFDEHeader fde;
} DebugFrameHeader;

/* Forward declarations for functions declared in tcg-target.c.inc and
   used here. */
static void tcg_target_init(TCGContext *s);
static const TCGTargetOpDef *tcg_target_op_def(TCGOpcode);
static void tcg_target_qemu_prologue(TCGContext *s);
static bool patch_reloc(tcg_insn_unit *code_ptr, int type,
                        intptr_t value, intptr_t addend);

static void tcg_register_jit_int(void *buf, size_t size,
                                 const void *debug_frame,
                                 size_t debug_frame_size)
    __attribute__((unused));

static const char *target_parse_constraint(TCGArgConstraint *ct,
                                           const char *ct_str, TCGType type);
static void tcg_out_ld(TCGContext *s, TCGType type, TCGReg ret, TCGReg arg1,
                       intptr_t arg2);
static bool tcg_out_mov(TCGContext *s, TCGType type, TCGReg ret, TCGReg arg);
static void tcg_out_movi(TCGContext *s, TCGType type,
                         TCGReg ret, tcg_target_long arg);
static void tcg_out_op(TCGContext *s, TCGOpcode opc, const TCGArg *args,
                       const BackendValType *arg_types);
#if TCG_TARGET_MAYBE_vec
static bool tcg_out_dup_vec(TCGContext *s, TCGType type, unsigned vece,
                            TCGReg dst, TCGReg src);
static bool tcg_out_dupm_vec(TCGContext *s, TCGType type, unsigned vece,
                             TCGReg dst, TCGReg base, intptr_t offset);
static void tcg_out_dupi_vec(TCGContext *s, TCGType type, unsigned vece,
                             TCGReg dst, int64_t arg);
static void tcg_out_vec_op(TCGContext *s, TCGOpcode opc, unsigned vecl,
                           unsigned vece, const TCGArg *args,
                           const BackendValType *arg_types);
#else
static inline bool tcg_out_dup_vec(TCGContext *s, TCGType type, unsigned vece,
                                   TCGReg dst, TCGReg src)
{
    g_assert_not_reached();
}
static inline bool tcg_out_dupm_vec(TCGContext *s, TCGType type, unsigned vece,
                                    TCGReg dst, TCGReg base, intptr_t offset)
{
    g_assert_not_reached();
}
static inline void tcg_out_dupi_vec(TCGContext *s, TCGType type, unsigned vece,
                                    TCGReg dst, int64_t arg)
{
    g_assert_not_reached();
}
static inline void tcg_out_vec_op(TCGContext *s, TCGOpcode opc, unsigned vecl,
                                  unsigned vece, const TCGArg *args,
                                  const BackendValType *arg_types)
{
    g_assert_not_reached();
}
#endif
static void tcg_out_st(TCGContext *s, TCGType type, TCGReg arg, TCGReg arg1,
                       intptr_t arg2);
static bool tcg_out_sti(TCGContext *s, TCGType type, TCGArg val,
                        TCGReg base, intptr_t ofs);
static void tcg_out_call(TCGContext *s, tcg_insn_unit *target);
static bool tcg_target_const_match(tcg_target_long val, TCGType type,
                                   const TCGArgConstraint *arg_ct);
#ifdef TCG_TARGET_NEED_SLOW_PATH_LABELS
static int tcg_out_slow_path_finalize(TCGContext *s);
#endif

#include "tcg-pool.c.inc"

#define TCG_HIGHWATER 1024

static TCGContext **tcg_ctxs;
static unsigned int n_tcg_ctxs;
TCGv_env cpu_env = 0;

struct tcg_region_tree {
    QemuMutex lock;
    GTree *tree;
    /* padding to avoid false sharing is computed at run-time */
};

/*
 * We divide code_gen_buffer into equally-sized "regions" that TCG threads
 * dynamically allocate from as demand dictates. Given appropriate region
 * sizing, this minimizes flushes even when some TCG threads generate a lot
 * more code than others.
 */
struct tcg_region_state {
    QemuMutex lock;

    /* fields set at init time */
    void *start;
    void *start_aligned;
    void *end;
    size_t n;
    size_t size; /* size of one region */
    size_t stride; /* .size + guard size */

    /* fields protected by the lock */
    size_t current; /* current region index */
    size_t agg_size_full; /* aggregate size of full regions */
};

static struct tcg_region_state region;
/*
 * This is an array of struct tcg_region_tree's, with padding.
 * We use void * to simplify the computation of region_trees[i]; each
 * struct is found every tree_size bytes.
 */
static void *region_trees;
static size_t tree_size;
static TCGRegSet tcg_target_available_regs[TCG_TYPE_COUNT];
static TCGRegSet tcg_target_call_clobber_regs;
static TCGRegSet tcg_target_tlb_check_clobber_regs;

#if TCG_TARGET_INSN_UNIT_SIZE == 1
static __attribute__((unused)) inline void tcg_out8(TCGContext *s, uint8_t v)
{
    *s->code_ptr++ = v;
}

static __attribute__((unused)) inline void tcg_patch8(tcg_insn_unit *p,
                                                      uint8_t v)
{
    *p = v;
}
#endif

#if TCG_TARGET_INSN_UNIT_SIZE <= 2
static __attribute__((unused)) inline void tcg_out16(TCGContext *s, uint16_t v)
{
    if (TCG_TARGET_INSN_UNIT_SIZE == 2) {
        *s->code_ptr++ = v;
    } else {
        tcg_insn_unit *p = s->code_ptr;
        memcpy(p, &v, sizeof(v));
        s->code_ptr = p + (2 / TCG_TARGET_INSN_UNIT_SIZE);
    }
}

static __attribute__((unused)) inline void tcg_patch16(tcg_insn_unit *p,
                                                       uint16_t v)
{
    if (TCG_TARGET_INSN_UNIT_SIZE == 2) {
        *p = v;
    } else {
        memcpy(p, &v, sizeof(v));
    }
}
#endif

#if TCG_TARGET_INSN_UNIT_SIZE <= 4
static __attribute__((unused)) inline void tcg_out32(TCGContext *s, uint32_t v)
{
    if (TCG_TARGET_INSN_UNIT_SIZE == 4) {
        *s->code_ptr++ = v;
    } else {
        tcg_insn_unit *p = s->code_ptr;
        memcpy(p, &v, sizeof(v));
        s->code_ptr = p + (4 / TCG_TARGET_INSN_UNIT_SIZE);
    }
}

static __attribute__((unused)) inline void tcg_patch32(tcg_insn_unit *p,
                                                       uint32_t v)
{
    if (TCG_TARGET_INSN_UNIT_SIZE == 4) {
        *p = v;
    } else {
        memcpy(p, &v, sizeof(v));
    }
}
#endif

#if TCG_TARGET_INSN_UNIT_SIZE <= 8
static __attribute__((unused)) inline void tcg_out64(TCGContext *s, uint64_t v)
{
    if (TCG_TARGET_INSN_UNIT_SIZE == 8) {
        *s->code_ptr++ = v;
    } else {
        tcg_insn_unit *p = s->code_ptr;
        memcpy(p, &v, sizeof(v));
        s->code_ptr = p + (8 / TCG_TARGET_INSN_UNIT_SIZE);
    }
}

static __attribute__((unused)) inline void tcg_patch64(tcg_insn_unit *p,
                                                       uint64_t v)
{
    if (TCG_TARGET_INSN_UNIT_SIZE == 8) {
        *p = v;
    } else {
        memcpy(p, &v, sizeof(v));
    }
}
#endif

/* label relocation processing */

static void tcg_out_reloc(TCGContext *s, tcg_insn_unit *code_ptr, int type,
                          TCGLabel *l, intptr_t addend)
{
    TCGRelocation *r = tcg_malloc(sizeof(TCGRelocation));

    r->type = type;
    r->ptr = code_ptr;
    r->addend = addend;
    QSIMPLEQ_INSERT_TAIL(&l->relocs, r, next);
}

static void tcg_out_label(TCGContext *s, TCGLabel *l, tcg_insn_unit *ptr)
{
    tcg_debug_assert(!l->has_value);
    l->has_value = 1;
    l->u.value_ptr = ptr;
}

TCGLabel *gen_new_label(void)
{
    TCGContext *s = tcg_ctx;
    TCGLabel *l = tcg_malloc(sizeof(TCGLabel));

    memset(l, 0, sizeof(TCGLabel));
    l->id = s->nb_labels++;
    QSIMPLEQ_INIT(&l->relocs);

    QSIMPLEQ_INSERT_TAIL(&s->labels, l, next);

    return l;
}

static bool tcg_resolve_relocs(TCGContext *s)
{
    TCGLabel *l;

    QSIMPLEQ_FOREACH(l, &s->labels, next) {
        TCGRelocation *r;
        uintptr_t value = l->u.value;

        QSIMPLEQ_FOREACH(r, &l->relocs, next) {
            if (!patch_reloc(r->ptr, r->type, value, r->addend)) {
                return false;
            }
        }
    }
    return true;
}

static void set_jmp_reset_offset(TCGContext *s, int which)
{
    /*
     * We will check for overflow at the end of the opcode loop in
     * tcg_gen_code, where we bound tcg_current_code_size to UINT16_MAX.
     */
    s->tb_jmp_reset_offset[which] = tcg_current_code_size(s);
}

/* compare a pointer @ptr and a tb_tc @s */
static int ptr_cmp_tb_tc(const void *ptr, const struct tb_tc *s)
{
    if (ptr >= s->ptr + s->size) {
        return 1;
    } else if (ptr < s->ptr) {
        return -1;
    }
    return 0;
}

static gint tb_tc_cmp(gconstpointer ap, gconstpointer bp, gpointer _)
{
    const struct tb_tc *a = ap;
    const struct tb_tc *b = bp;

    /*
     * When both sizes are set, we know this isn't a lookup.
     * This is the most likely case: every TB must be inserted; lookups
     * are a lot less frequent.
     */
    if (likely(a->size && b->size)) {
        if (a->ptr > b->ptr) {
            return 1;
        } else if (a->ptr < b->ptr) {
            return -1;
        }
        /* a->ptr == b->ptr should happen only on deletions */
        g_assert(a->size == b->size);
        return 0;
    }
    /*
     * All lookups have either .size field set to 0.
     * From the glib sources we see that @ap is always the lookup key. However
     * the docs provide no guarantee, so we just mark this case as likely.
     */
    if (likely(a->size == 0)) {
        return ptr_cmp_tb_tc(a->ptr, b);
    }
    return ptr_cmp_tb_tc(b->ptr, a);
}

static void tcg_tb_destroy(gpointer _tb)
{
    TranslationBlock *tb = (TranslationBlock *) _tb;

    qemu_spin_destroy(&tb->jmp_lock);
    if (tb->bailout_info) {
        tcg_debug_assert(tb->cflags & CF_BAILOUT_MASK);
        g_free(tb->bailout_info);
    }
}

static void tcg_region_trees_init(void)
{
    size_t i;

    tree_size = ROUND_UP(sizeof(struct tcg_region_tree), qemu_dcache_linesize);
    region_trees = qemu_memalign(qemu_dcache_linesize, region.n * tree_size);
    for (i = 0; i < region.n; i++) {
        struct tcg_region_tree *rt = region_trees + i * tree_size;

        qemu_mutex_init(&rt->lock);
        rt->tree = g_tree_new_full(tb_tc_cmp, NULL, NULL, tcg_tb_destroy);
    }
}

static struct tcg_region_tree *tc_ptr_to_region_tree(void *p)
{
    size_t region_idx;

    if (p < region.start_aligned) {
        region_idx = 0;
    } else {
        ptrdiff_t offset = p - region.start_aligned;

        if (offset > region.stride * (region.n - 1)) {
            region_idx = region.n - 1;
        } else {
            region_idx = offset / region.stride;
        }
    }
    return region_trees + region_idx * tree_size;
}

void tcg_tb_insert(TranslationBlock *tb)
{
    struct tcg_region_tree *rt = tc_ptr_to_region_tree(tb->tc.ptr);

    qemu_mutex_lock(&rt->lock);
    g_tree_insert(rt->tree, &tb->tc, tb);
    qemu_mutex_unlock(&rt->lock);
}

void tcg_tb_remove(TranslationBlock *tb)
{
    struct tcg_region_tree *rt = tc_ptr_to_region_tree(tb->tc.ptr);

    qemu_mutex_lock(&rt->lock);
    g_tree_remove(rt->tree, &tb->tc);
    qemu_mutex_unlock(&rt->lock);
}

/*
 * Find the TB 'tb' such that
 * tb->tc.ptr <= tc_ptr < tb->tc.ptr + tb->tc.size
 * Return NULL if not found.
 */
TranslationBlock *tcg_tb_lookup(uintptr_t tc_ptr)
{
    struct tcg_region_tree *rt = tc_ptr_to_region_tree((void *)tc_ptr);
    TranslationBlock *tb;
    struct tb_tc s = { .ptr = (void *)tc_ptr };

    qemu_mutex_lock(&rt->lock);
    tb = g_tree_lookup(rt->tree, &s);
    qemu_mutex_unlock(&rt->lock);
    return tb;
}

static void tcg_region_tree_lock_all(void)
{
    size_t i;

    for (i = 0; i < region.n; i++) {
        struct tcg_region_tree *rt = region_trees + i * tree_size;

        qemu_mutex_lock(&rt->lock);
    }
}

static void tcg_region_tree_unlock_all(void)
{
    size_t i;

    for (i = 0; i < region.n; i++) {
        struct tcg_region_tree *rt = region_trees + i * tree_size;

        qemu_mutex_unlock(&rt->lock);
    }
}

void tcg_tb_foreach(GTraverseFunc func, gpointer user_data)
{
    size_t i;

    tcg_region_tree_lock_all();
    for (i = 0; i < region.n; i++) {
        struct tcg_region_tree *rt = region_trees + i * tree_size;

        g_tree_foreach(rt->tree, func, user_data);
    }
    tcg_region_tree_unlock_all();
}

size_t tcg_nb_tbs(void)
{
    size_t nb_tbs = 0;
    size_t i;

    tcg_region_tree_lock_all();
    for (i = 0; i < region.n; i++) {
        struct tcg_region_tree *rt = region_trees + i * tree_size;

        nb_tbs += g_tree_nnodes(rt->tree);
    }
    tcg_region_tree_unlock_all();
    return nb_tbs;
}

static void tcg_region_tree_reset_all(void)
{
    size_t i;

    tcg_region_tree_lock_all();
    for (i = 0; i < region.n; i++) {
        struct tcg_region_tree *rt = region_trees + i * tree_size;

        /* Increment the refcount first so that destroy acts as a reset */
        g_tree_ref(rt->tree);
        g_tree_destroy(rt->tree);
    }
    tcg_region_tree_unlock_all();
}

static void tcg_region_bounds(size_t curr_region, void **pstart, void **pend)
{
    void *start, *end;

    start = region.start_aligned + curr_region * region.stride;
    end = start + region.size;

    if (curr_region == 0) {
        start = region.start;
    }
    if (curr_region == region.n - 1) {
        end = region.end;
    }

    *pstart = start;
    *pend = end;
}

static void tcg_region_assign(TCGContext *s, size_t curr_region)
{
    void *start, *end;

    tcg_region_bounds(curr_region, &start, &end);

    s->code_gen_buffer = start;
    s->code_gen_ptr = start;
    s->code_gen_buffer_size = end - start;
    s->code_gen_highwater = end - TCG_HIGHWATER;
}

static bool tcg_region_alloc__locked(TCGContext *s)
{
    if (region.current == region.n) {
        return true;
    }
    tcg_region_assign(s, region.current);
    region.current++;
    return false;
}

/*
 * Request a new region once the one in use has filled up.
 * Returns true on error.
 */
static bool tcg_region_alloc(TCGContext *s)
{
    bool err;
    /* read the region size now; alloc__locked will overwrite it on success */
    size_t size_full = s->code_gen_buffer_size;

    qemu_mutex_lock(&region.lock);
    err = tcg_region_alloc__locked(s);
    if (!err) {
        region.agg_size_full += size_full - TCG_HIGHWATER;
    }
    qemu_mutex_unlock(&region.lock);
    return err;
}

/*
 * Perform a context's first region allocation.
 * This function does _not_ increment region.agg_size_full.
 */
static inline bool tcg_region_initial_alloc__locked(TCGContext *s)
{
    return tcg_region_alloc__locked(s);
}

/* Call from a safe-work context */
void tcg_region_reset_all(void)
{
    unsigned int n_ctxs = qatomic_read(&n_tcg_ctxs);
    unsigned int i;

    qemu_mutex_lock(&region.lock);
    region.current = 0;
    region.agg_size_full = 0;

    for (i = 0; i < n_ctxs; i++) {
        TCGContext *s = qatomic_read(&tcg_ctxs[i]);
        bool err = tcg_region_initial_alloc__locked(s);

        g_assert(!err);
    }
    qemu_mutex_unlock(&region.lock);

    tcg_region_tree_reset_all();
}

#ifdef CONFIG_USER_ONLY
static size_t tcg_n_regions(void)
{
    return 1;
}
#else
/*
 * It is likely that some vCPUs will translate more code than others, so we
 * first try to set more regions than max_cpus, with those regions being of
 * reasonable size. If that's not possible we make do by evenly dividing
 * the code_gen_buffer among the vCPUs.
 */
static size_t tcg_n_regions(void)
{
    size_t i;

    /* Use a single region if all we have is one vCPU thread */
#if !defined(CONFIG_USER_ONLY)
    MachineState *ms = MACHINE(qdev_get_machine());
    unsigned int max_cpus = ms->smp.max_cpus;
#endif
    if (max_cpus == 1 || !qemu_tcg_mttcg_enabled()) {
        return 1;
    }

    /* Try to have more regions than max_cpus, with each region being >= 2 MB */
    for (i = 8; i > 0; i--) {
        size_t regions_per_thread = i;
        size_t region_size;

        region_size = tcg_init_ctx.code_gen_buffer_size;
        region_size /= max_cpus * regions_per_thread;

        if (region_size >= 2 * 1024u * 1024) {
            return max_cpus * regions_per_thread;
        }
    }
    /* If we can't, then just allocate one region per vCPU thread */
    return max_cpus;
}
#endif

/*
 * Initializes region partitioning.
 *
 * Called at init time from the parent thread (i.e. the one calling
 * tcg_context_init), after the target's TCG globals have been set.
 *
 * Region partitioning works by splitting code_gen_buffer into separate regions,
 * and then assigning regions to TCG threads so that the threads can translate
 * code in parallel without synchronization.
 *
 * In softmmu the number of TCG threads is bounded by max_cpus, so we use at
 * least max_cpus regions in MTTCG. In !MTTCG we use a single region.
 * Note that the TCG options from the command-line (i.e. -accel accel=tcg,[...])
 * must have been parsed before calling this function, since it calls
 * qemu_tcg_mttcg_enabled().
 *
 * In user-mode we use a single region.  Having multiple regions in user-mode
 * is not supported, because the number of vCPU threads (recall that each thread
 * spawned by the guest corresponds to a vCPU thread) is only bounded by the
 * OS, and usually this number is huge (tens of thousands is not uncommon).
 * Thus, given this large bound on the number of vCPU threads and the fact
 * that code_gen_buffer is allocated at compile-time, we cannot guarantee
 * that the availability of at least one region per vCPU thread.
 *
 * However, this user-mode limitation is unlikely to be a significant problem
 * in practice. Multi-threaded guests share most if not all of their translated
 * code, which makes parallel code generation less appealing than in softmmu.
 */
void tcg_region_init(void)
{
    void *buf = tcg_init_ctx.code_gen_buffer;
    void *aligned;
    size_t size = tcg_init_ctx.code_gen_buffer_size;
    size_t page_size = qemu_real_host_page_size;
    size_t region_size;
    size_t n_regions;
    size_t i;

    n_regions = tcg_n_regions();

    /* The first region will be 'aligned - buf' bytes larger than the others */
    aligned = QEMU_ALIGN_PTR_UP(buf, page_size);
    g_assert(aligned < tcg_init_ctx.code_gen_buffer + size);
    /*
     * Make region_size a multiple of page_size, using aligned as the start.
     * As a result of this we might end up with a few extra pages at the end of
     * the buffer; we will assign those to the last region.
     */
    region_size = (size - (aligned - buf)) / n_regions;
    region_size = QEMU_ALIGN_DOWN(region_size, page_size);

    /* A region must have at least 2 pages; one code, one guard */
    g_assert(region_size >= 2 * page_size);

    /* init the region struct */
    qemu_mutex_init(&region.lock);
    region.n = n_regions;
    region.size = region_size - page_size;
    region.stride = region_size;
    region.start = buf;
    region.start_aligned = aligned;
    /* page-align the end, since its last page will be a guard page */
    region.end = QEMU_ALIGN_PTR_DOWN(buf + size, page_size);
    /* account for that last guard page */
    region.end -= page_size;

    /* set guard pages */
    for (i = 0; i < region.n; i++) {
        void *start, *end;
        int rc;

        tcg_region_bounds(i, &start, &end);
        rc = qemu_mprotect_none(end, page_size);
        g_assert(!rc);
    }

    tcg_region_trees_init();

    /* In user-mode we support only one ctx, so do the initial allocation now */
#ifdef CONFIG_USER_ONLY
    {
        bool err = tcg_region_initial_alloc__locked(tcg_ctx);

        g_assert(!err);
    }
#endif
}

static void alloc_tcg_plugin_context(TCGContext *s)
{
#ifdef CONFIG_PLUGIN
    s->plugin_tb = g_new0(struct qemu_plugin_tb, 1);
    s->plugin_tb->insns =
        g_ptr_array_new_with_free_func(qemu_plugin_insn_cleanup_fn);
#endif
}

/*
 * All TCG threads except the parent (i.e. the one that called tcg_context_init
 * and registered the target's TCG globals) must register with this function
 * before initiating translation.
 *
 * In user-mode we just point tcg_ctx to tcg_init_ctx. See the documentation
 * of tcg_region_init() for the reasoning behind this.
 *
 * In softmmu each caller registers its context in tcg_ctxs[]. Note that in
 * softmmu tcg_ctxs[] does not track tcg_ctx_init, since the initial context
 * is not used anymore for translation once this function is called.
 *
 * Not tracking tcg_init_ctx in tcg_ctxs[] in softmmu keeps code that iterates
 * over the array (e.g. tcg_code_size() the same for both softmmu and user-mode.
 */
#ifdef CONFIG_USER_ONLY
void tcg_register_thread(void)
{
    tcg_ctx = &tcg_init_ctx;
}
#else
void tcg_register_thread(void)
{
    MachineState *ms = MACHINE(qdev_get_machine());
    TCGContext *s = g_malloc(sizeof(*s));
    unsigned int i, n;
    bool err;

    *s = tcg_init_ctx;

    /* Relink mem_base.  */
    for (i = 0, n = tcg_init_ctx.nb_globals; i < n; ++i) {
        if (tcg_init_ctx.temps[i].mem_base) {
            ptrdiff_t b = tcg_init_ctx.temps[i].mem_base - tcg_init_ctx.temps;
            tcg_debug_assert(b >= 0 && b < n);
            s->temps[i].mem_base = &s->temps[b];
        }
    }
    /* Relink frame_temp.  */
    s->frame_temp = &s->temps[tcg_init_ctx.frame_temp - tcg_init_ctx.temps];

    /* Claim an entry in tcg_ctxs */
    n = qatomic_fetch_inc(&n_tcg_ctxs);
    g_assert(n < ms->smp.max_cpus);
    qatomic_set(&tcg_ctxs[n], s);

    if (n > 0) {
        alloc_tcg_plugin_context(s);
    }

    tcg_ctx = s;
    qemu_mutex_lock(&region.lock);
    err = tcg_region_initial_alloc__locked(tcg_ctx);
    g_assert(!err);
    qemu_mutex_unlock(&region.lock);

    tcg_ctx->tb_set = g_hash_table_new(NULL, NULL);
}
#endif /* !CONFIG_USER_ONLY */

/*
 * Returns the size (in bytes) of all translated code (i.e. from all regions)
 * currently in the cache.
 * See also: tcg_code_capacity()
 * Do not confuse with tcg_current_code_size(); that one applies to a single
 * TCG context.
 */
size_t tcg_code_size(void)
{
    unsigned int n_ctxs = qatomic_read(&n_tcg_ctxs);
    unsigned int i;
    size_t total;

    qemu_mutex_lock(&region.lock);
    total = region.agg_size_full;
    for (i = 0; i < n_ctxs; i++) {
        const TCGContext *s = qatomic_read(&tcg_ctxs[i]);
        size_t size;

        size = qatomic_read(&s->code_gen_ptr) - s->code_gen_buffer;
        g_assert(size <= s->code_gen_buffer_size);
        total += size;
    }
    qemu_mutex_unlock(&region.lock);
    return total;
}

/*
 * Returns the code capacity (in bytes) of the entire cache, i.e. including all
 * regions.
 * See also: tcg_code_size()
 */
size_t tcg_code_capacity(void)
{
    size_t guard_size, capacity;

    /* no need for synchronization; these variables are set at init time */
    guard_size = region.stride - region.size;
    capacity = region.end + guard_size - region.start;
    capacity -= region.n * (guard_size + TCG_HIGHWATER);
    return capacity;
}

size_t tcg_tb_phys_invalidate_count(void)
{
    unsigned int n_ctxs = qatomic_read(&n_tcg_ctxs);
    unsigned int i;
    size_t total = 0;

    for (i = 0; i < n_ctxs; i++) {
        const TCGContext *s = qatomic_read(&tcg_ctxs[i]);

        total += qatomic_read(&s->tb_phys_invalidate_count);
    }
    return total;
}

/* pool based memory allocation */
void *tcg_malloc_internal(TCGContext *s, int size)
{
    TCGPool *p;
    int pool_size;

    if (size > TCG_POOL_CHUNK_SIZE) {
        /* big malloc: insert a new pool (XXX: could optimize) */
        p = g_malloc(sizeof(TCGPool) + size);
        p->size = size;
        p->next = s->pool_first_large;
        s->pool_first_large = p;
        return p->data;
    } else {
        p = s->pool_current;
        if (!p) {
            p = s->pool_first;
            if (!p)
                goto new_pool;
        } else {
            if (!p->next) {
            new_pool:
                pool_size = TCG_POOL_CHUNK_SIZE;
                p = g_malloc(sizeof(TCGPool) + pool_size);
                p->size = pool_size;
                p->next = NULL;
                if (s->pool_current)
                    s->pool_current->next = p;
                else
                    s->pool_first = p;
            } else {
                p = p->next;
            }
        }
    }
    s->pool_current = p;
    s->pool_cur = p->data + size;
    s->pool_end = p->data + p->size;
    return p->data;
}

void tcg_pool_reset(TCGContext *s)
{
    TCGPool *p, *t;
    for (p = s->pool_first_large; p; p = t) {
        t = p->next;
        g_free(p);
    }
    s->pool_first_large = NULL;
    s->pool_cur = s->pool_end = NULL;
    s->pool_current = NULL;
}

typedef struct TCGHelperInfo {
    void *func;
    const char *name;
    unsigned flags;
    unsigned sizemask;
} TCGHelperInfo;

#include "exec/helper-proto.h"

static const TCGHelperInfo all_helpers[] = {
#include "exec/helper-tcg.h"
};
static GHashTable *helper_table;

#include "tcg-target-abi.c.inc"
static TCGReg indirect_reg_alloc_order[ARRAY_SIZE(tcg_target_reg_alloc_order)];
static void process_op_defs(TCGContext *s);
static TCGTemp *tcg_global_reg_new_internal(TCGContext *s, TCGType type,
                                            TCGReg reg, const char *name);

void tcg_context_init(TCGContext *s)
{
    int op, total_args, n, i;
    TCGOpDef *def;
    TCGArgConstraint *args_ct;
    TCGTemp *ts;

    memset(s, 0, sizeof(*s));
    s->nb_globals = 0;

    /* Count total number of arguments and allocate the corresponding
       space */
    total_args = 0;
    for(op = 0; op < NB_OPS; op++) {
        def = &tcg_op_defs[op];
        n = def->nb_iargs + def->nb_oargs;
        total_args += n;
    }

    args_ct = g_new0(TCGArgConstraint, total_args);

    for(op = 0; op < NB_OPS; op++) {
        def = &tcg_op_defs[op];
        def->args_ct = args_ct;
        n = def->nb_iargs + def->nb_oargs;
        args_ct += n;
    }

    /* Register helpers.  */
    /* Use g_direct_hash/equal for direct pointer comparisons on func.  */
    helper_table = g_hash_table_new(NULL, NULL);

    for (i = 0; i < ARRAY_SIZE(all_helpers); ++i) {
        g_hash_table_insert(helper_table, (gpointer)all_helpers[i].func,
                            (gpointer)&all_helpers[i]);
    }

    tcg_target_init(s);
    process_op_defs(s);

    /* Reverse the order of the saved registers, assuming they're all at
       the start of tcg_target_reg_alloc_order.  */
    for (n = 0; n < ARRAY_SIZE(tcg_target_reg_alloc_order); ++n) {
        int r = tcg_target_reg_alloc_order[n];
        if (tcg_regset_test_reg(tcg_target_call_clobber_regs, r)) {
            break;
        }
    }
    for (i = 0; i < n; ++i) {
        indirect_reg_alloc_order[i] = tcg_target_reg_alloc_order[n - 1 - i];
    }
    for (; i < ARRAY_SIZE(tcg_target_reg_alloc_order); ++i) {
        indirect_reg_alloc_order[i] = tcg_target_reg_alloc_order[i];
    }

    alloc_tcg_plugin_context(s);

    tcg_ctx = s;
    /*
     * In user-mode we simply share the init context among threads, since we
     * use a single region. See the documentation tcg_region_init() for the
     * reasoning behind this.
     * In softmmu we will have at most max_cpus TCG threads.
     */
#ifdef CONFIG_USER_ONLY
    tcg_ctxs = &tcg_ctx;
    n_tcg_ctxs = 1;
#else
    MachineState *ms = MACHINE(qdev_get_machine());
    unsigned int max_cpus = ms->smp.max_cpus;
    tcg_ctxs = g_new(TCGContext *, max_cpus);
#endif

    tcg_debug_assert(!tcg_regset_test_reg(s->reserved_regs, TCG_AREG0));
    ts = tcg_global_reg_new_internal(s, TCG_TYPE_PTR, TCG_AREG0, "env");
    cpu_env = temp_tcgv_ptr(ts);
}

/*
 * Allocate TBs right before their corresponding translated code, making
 * sure that TBs and code are on different cache lines.
 */
TranslationBlock *tcg_tb_alloc(TCGContext *s)
{
    uintptr_t align = qemu_icache_linesize;
    TranslationBlock *tb;
    void *next;

retry:
    /* Do be careful when update this. It is now assumed by tb_link_page()
     * that "tb->tc.ptr - ROUNDUP(sizeof(TranslationBlock), align) == tb".  */
    tb = (void *) ROUND_UP((uintptr_t) s->code_gen_ptr, align);
    next = (void *) ROUND_UP((uintptr_t) (tb + 1), align);

    if (unlikely(next > s->code_gen_highwater)) {
        if (tcg_region_alloc(s)) {
            return NULL;
        }
        goto retry;
    }
    qatomic_set(&s->code_gen_ptr, next);
    s->data_gen_ptr = NULL;
    return tb;
}

void tcg_prologue_init(TCGContext *s)
{
    size_t prologue_size, total_size;
    void *buf0, *buf1;

    /* Put the prologue at the beginning of code_gen_buffer.  */
    buf0 = s->code_gen_buffer;
    total_size = s->code_gen_buffer_size;
    s->code_ptr = buf0;
    s->code_buf = buf0;
    s->data_gen_ptr = NULL;
    s->code_gen_prologue = buf0;

    /* Compute a high-water mark, at which we voluntarily flush the buffer
       and start over.  The size here is arbitrary, significantly larger
       than we expect the code generation for any one opcode to require.  */
    s->code_gen_highwater = s->code_gen_buffer + (total_size - TCG_HIGHWATER);

#ifdef TCG_TARGET_NEED_POOL_LABELS
    s->pool_labels = NULL;
#endif

    /* Generate the prologue.  */
    tcg_target_qemu_prologue(s);

#ifdef TCG_TARGET_NEED_POOL_LABELS
    /* Allow the prologue to put e.g. guest_base into a pool entry.  */
    {
        int result = tcg_out_pool_finalize(s);
        tcg_debug_assert(result == 0);
    }
#endif

    buf1 = s->code_ptr;
    flush_icache_range((uintptr_t)buf0, (uintptr_t)buf1);

    /* Deduct the prologue from the buffer.  */
    prologue_size = tcg_current_code_size(s);
    s->code_gen_ptr = buf1;
    s->code_gen_buffer = buf1;
    s->code_buf = buf1;
    total_size -= prologue_size;
    s->code_gen_buffer_size = total_size;

    tcg_register_jit(s->code_gen_buffer, total_size);

#ifdef DEBUG_DISAS
    if (qemu_loglevel_mask(CPU_LOG_TB_OUT_ASM)) {
        FILE *logfile = qemu_log_lock();
        qemu_log("PROLOGUE: [size=%zu]\n", prologue_size);
        if (s->data_gen_ptr) {
            size_t code_size = s->data_gen_ptr - buf0;
            size_t data_size = prologue_size - code_size;
            size_t i;

            log_disas(buf0, code_size);

            for (i = 0; i < data_size; i += sizeof(tcg_target_ulong)) {
                if (sizeof(tcg_target_ulong) == 8) {
                    qemu_log("0x%08" PRIxPTR ":  .quad  0x%016" PRIx64 "\n",
                             (uintptr_t)s->data_gen_ptr + i,
                             *(uint64_t *)(s->data_gen_ptr + i));
                } else {
                    qemu_log("0x%08" PRIxPTR ":  .long  0x%08x\n",
                             (uintptr_t)s->data_gen_ptr + i,
                             *(uint32_t *)(s->data_gen_ptr + i));
                }
            }
        } else {
            log_disas(buf0, prologue_size);
        }
        qemu_log("\n");
        qemu_log_flush();
        qemu_log_unlock(logfile);
    }
#endif

    /* Assert that goto_ptr is implemented completely.  */
    if (TCG_TARGET_HAS_goto_ptr) {
        tcg_debug_assert(s->code_gen_epilogue != NULL);
    }
}

void tcg_func_start(TCGContext *s)
{
    tcg_pool_reset(s);
    /* No constant temps have been previously allocated. */
    for (int i = 0; i < TCG_TYPE_COUNT; ++i) {
        if (s->const_table[i]) {
            g_hash_table_remove_all(s->const_table[i]);
        }
    }

    s->nb_temps = s->nb_globals;
    s->nb_ops = 0;
    s->nb_labels = 0;
    s->current_frame_offset = s->frame_start;
#ifdef CONFIG_DEBUG_TCG
    s->goto_tb_issue_mask = 0;
#endif

    QTAILQ_INIT(&s->ops);
    QTAILQ_INIT(&s->free_ops);
    QSIMPLEQ_INIT(&s->labels);
}

static void tcg_signal_tb_overflow__siglongjmp(TCGContext *s)
{
    if (!s->trace) {
        /* Signal overflow, starting over with fewer guest insns.  */
        siglongjmp(s->jmp_trans, -2);
    } else {
        /* Too bad that it's almost impossible to fix in trace recording mode
         * since retranslation is necessary. Expected to be really hurt.  */
        qemu_log_mask(CPU_LOG_TB_OP | CPU_LOG_TB_OP_OPT,
                      "Exit cpu loop due to TB overflow within trace recording "
                      "mode (nb_temps: %d)\n", s->nb_temps);
        s->head_tb = NULL;
        cpu_loop_exit_noexc(current_cpu);
    }
}

static TCGTemp *tcg_temp_alloc(TCGContext *s, TCGType type, TCGTempKind kind)
{
    uint32_t n = s->nb_temps++;
    TCGTemp *ts = &s->temps[n];

    if (unlikely(n >= TCG_MAX_TEMPS)) {
        tcg_signal_tb_overflow__siglongjmp(s);
    }
    memset(ts, 0, offsetof(TCGTemp, end_reset_fields));
    ts->type = type;
    ts->kind = kind;
    return ts;
}

static TCGTemp *tcg_global_alloc(TCGContext *s, TCGType type, bool fixed)
{
    TCGTemp *ts;
    TCGTempKind kind = fixed ? TEMP_FIXED : TEMP_GLOBAL;

    tcg_debug_assert(s->nb_globals == s->nb_temps);
    tcg_debug_assert(s->nb_globals < TCG_MAX_TEMPS);
    s->nb_globals++;
    ts = tcg_temp_alloc(s, type, kind);
    return ts;
}

static TCGTemp *tcg_global_reg_new_internal(TCGContext *s, TCGType type,
                                            TCGReg reg, const char *name)
{
    TCGTemp *ts;

    _Static_assert(TCG_TARGET_REG_BITS == 64);

    ts = tcg_global_alloc(s, type, true);
    ts->reg = reg;
    ts->name = name;
    tcg_regset_set_reg(s->reserved_regs, reg);
    return ts;
}

void tcg_set_frame(TCGContext *s, TCGReg reg, intptr_t start, intptr_t size)
{
    s->frame_start = start;
    s->frame_end = start + size;
    s->frame_temp
        = tcg_global_reg_new_internal(s, TCG_TYPE_PTR, reg, "_frame");
}

TCGTemp *tcg_global_mem_new_internal(TCGType type, TCGv_ptr base,
                                     intptr_t offset, const char *name)
{
    TCGContext *s = tcg_ctx;
    TCGTemp *base_ts = tcgv_ptr_temp(base);
    bool indirect_reg = false;
    TCGTemp *ts;

    _Static_assert(TCG_TARGET_REG_BITS == 64);

    switch (__builtin_expect(base_ts->kind, TEMP_FIXED)) {
    case TEMP_FIXED:
        break;
    case TEMP_GLOBAL:
        /* We do not support double-indirect registers.  */
        tcg_debug_assert(!base_ts->indirect_reg);
        base_ts->indirect_base = true;
        s->nb_indirects++;
        indirect_reg = true;
        break;
    default:
        g_assert_not_reached();
    }

    ts = tcg_global_alloc(s, type, false);
    ts->indirect_reg = indirect_reg;
    ts->mem_allocated = true;
    ts->mem_base = base_ts;
    ts->mem_offset = offset;
    ts->name = name;
    return ts;
}

TCGTemp *tcg_temp_new_internal(TCGType type, TCGTempKind kind)
{
    TCGContext *s = tcg_ctx;
    TCGTemp *ts;

    ts = tcg_temp_alloc(s, type, kind);
#if defined(CONFIG_DEBUG_TCG)
    ts->temp_allocated = true;
    if (kind <= TEMP_LOCAL) {
        s->temps_in_use++;
    }
#endif
    return ts;
}

TCGv_vec tcg_temp_new_vec(TCGType type)
{
    TCGTemp *t;

#ifdef CONFIG_DEBUG_TCG
    switch (type) {
    case TCG_TYPE_V64:
        assert(TCG_TARGET_HAS_v64);
        break;
    case TCG_TYPE_V128:
        assert(TCG_TARGET_HAS_v128);
        break;
    case TCG_TYPE_V256:
        assert(TCG_TARGET_HAS_v256);
        break;
    default:
        g_assert_not_reached();
    }
#endif

    t = tcg_temp_new_internal(type, TEMP_NORMAL);
    return temp_tcgv_vec(t);
}

/* Create a new temp of the same type as an existing temp.  */
TCGv_vec tcg_temp_new_vec_matching(TCGv_vec match)
{
    TCGTemp *t = tcgv_vec_temp(match);

    tcg_debug_assert(t->temp_allocated);
    t = tcg_temp_new_internal(t->base_type, TEMP_NORMAL);
    return temp_tcgv_vec(t);
}

void tcg_temp_free_internal(TCGTemp *ts)
{
    /* In order to simplify users of tcg_constant_*, silently ignore free.  */
    if (ts->kind == TEMP_CONST) {
        return;
    }

#if defined(CONFIG_DEBUG_TCG)
    tcg_ctx->temps_in_use--;
    if (tcg_ctx->temps_in_use < 0) {
        fprintf(stderr, "More temporaries freed than allocated!\n");
    }
    tcg_debug_assert(ts->kind < TEMP_GLOBAL);
    tcg_debug_assert(ts->temp_allocated);
    ts->temp_allocated = false;
#endif
}

bool tcg_constant_internal(TCGType type, int64_t val, TCGTemp **pts)
{
    TCGContext *s = tcg_ctx;
    GHashTable *h = s->const_table[type];
    TCGTemp *ts;
    bool not_found;

    if (h == NULL) {
        h = g_hash_table_new(g_int64_hash, g_int64_equal);
        s->const_table[type] = h;
    }

    ts = g_hash_table_lookup(h, &val);
    if ((not_found = ts == NULL)) {
        ts = tcg_temp_new_internal(type, TEMP_CONST);
        ts->val = val;
        g_hash_table_insert(h, &ts->val, ts);
    }
    *pts = ts;
    return not_found;
}

TCGv_vec tcg_constant_vec(TCGType type, unsigned vece, int64_t val)
{
    TCGTemp *ts;
    tcg_constant_internal(type, dup_const(vece, val), &ts);
    return temp_tcgv_vec(ts);
}

TCGv_vec tcg_constant_vec_matching(TCGv_vec match, unsigned vece, int64_t val)
{
    TCGTemp *t = tcgv_vec_temp(match);

    tcg_debug_assert(t->temp_allocated);
    return tcg_constant_vec(t->base_type, vece, val);
}

TCGv_i32 tcg_const_i32(int32_t val)
{
    TCGv_i32 t0;
    t0 = tcg_temp_new_i32();
    tcg_gen_movi_i32(t0, val);
    return t0;
}

TCGv_i64 tcg_const_i64(int64_t val)
{
    TCGv_i64 t0;
    t0 = tcg_temp_new_i64();
    tcg_gen_movi_i64(t0, val);
    return t0;
}

TCGv_i32 tcg_const_local_i32(int32_t val)
{
    TCGv_i32 t0;
    t0 = tcg_temp_local_new_i32();
    tcg_gen_movi_i32(t0, val);
    return t0;
}

TCGv_i64 tcg_const_local_i64(int64_t val)
{
    TCGv_i64 t0;
    t0 = tcg_temp_local_new_i64();
    tcg_gen_movi_i64(t0, val);
    return t0;
}

#if defined(CONFIG_DEBUG_TCG)
void tcg_clear_temp_count(void)
{
    TCGContext *s = tcg_ctx;
    s->temps_in_use = 0;
}

int tcg_check_temp_count(void)
{
    TCGContext *s = tcg_ctx;
    if (s->temps_in_use) {
        /* Clear the count so that we don't give another
         * warning immediately next time around.
         */
        s->temps_in_use = 0;
        return 1;
    }
    return 0;
}
#endif

/* Return true if codegen of OP should be handled by tcg_reg_alloc_op().  */
static bool tcg_op_supported_by_backend(TCGOpcode op)
{
    const bool have_vec
        = TCG_TARGET_HAS_v64 | TCG_TARGET_HAS_v128 | TCG_TARGET_HAS_v256;

    switch (op) {
    case INDEX_op_discard:
    case INDEX_op_set_label:
    case INDEX_op_call:
    case INDEX_op_insn_start:
    case INDEX_op_mov_i32:
    case INDEX_op_mov_i64:
    case INDEX_op_mov_vec:
    case INDEX_op_dup_vec:
    case INDEX_op_side_effect:
        return false;

    case INDEX_op_br:
    case INDEX_op_mb:
    case INDEX_op_exit_tb:
    case INDEX_op_goto_tb:
    case INDEX_op_qemu_ld_i32:
    case INDEX_op_qemu_st_i32:
    case INDEX_op_qemu_ld_i64:
    case INDEX_op_qemu_st_i64:
        return true;

    case INDEX_op_goto_ptr:
        return TCG_TARGET_HAS_goto_ptr;

    case INDEX_op_setcond_i32:
    case INDEX_op_brcond_i32:
    case INDEX_op_ld8u_i32:
    case INDEX_op_ld8s_i32:
    case INDEX_op_ld16u_i32:
    case INDEX_op_ld16s_i32:
    case INDEX_op_ld_i32:
    case INDEX_op_st8_i32:
    case INDEX_op_st16_i32:
    case INDEX_op_st_i32:
    case INDEX_op_add_i32:
    case INDEX_op_sub_i32:
    case INDEX_op_mul_i32:
    case INDEX_op_and_i32:
    case INDEX_op_or_i32:
    case INDEX_op_xor_i32:
    case INDEX_op_shl_i32:
    case INDEX_op_shr_i32:
    case INDEX_op_sar_i32:
        return true;

    case INDEX_op_movcond_i32:
        return TCG_TARGET_HAS_movcond_i32;
    case INDEX_op_div_i32:
    case INDEX_op_divu_i32:
        return TCG_TARGET_HAS_div_i32;
    case INDEX_op_rem_i32:
    case INDEX_op_remu_i32:
        return TCG_TARGET_HAS_rem_i32;
    case INDEX_op_div2_i32:
    case INDEX_op_divu2_i32:
        return TCG_TARGET_HAS_div2_i32;
    case INDEX_op_rotl_i32:
    case INDEX_op_rotr_i32:
        return TCG_TARGET_HAS_rot_i32;
    case INDEX_op_deposit_i32:
        return TCG_TARGET_HAS_deposit_i32;
    case INDEX_op_extract_i32:
        return TCG_TARGET_HAS_extract_i32;
    case INDEX_op_sextract_i32:
        return TCG_TARGET_HAS_sextract_i32;
    case INDEX_op_extract2_i32:
        return TCG_TARGET_HAS_extract2_i32;
    case INDEX_op_add2_i32:
        return TCG_TARGET_HAS_add2_i32;
    case INDEX_op_sub2_i32:
        return TCG_TARGET_HAS_sub2_i32;
    case INDEX_op_mulu2_i32:
        return TCG_TARGET_HAS_mulu2_i32;
    case INDEX_op_muls2_i32:
        return TCG_TARGET_HAS_muls2_i32;
    case INDEX_op_muluh_i32:
        return TCG_TARGET_HAS_muluh_i32;
    case INDEX_op_mulsh_i32:
        return TCG_TARGET_HAS_mulsh_i32;
    case INDEX_op_ext8s_i32:
        return TCG_TARGET_HAS_ext8s_i32;
    case INDEX_op_ext16s_i32:
        return TCG_TARGET_HAS_ext16s_i32;
    case INDEX_op_ext8u_i32:
        return TCG_TARGET_HAS_ext8u_i32;
    case INDEX_op_ext16u_i32:
        return TCG_TARGET_HAS_ext16u_i32;
    case INDEX_op_bswap16_i32:
        return TCG_TARGET_HAS_bswap16_i32;
    case INDEX_op_bswap32_i32:
        return TCG_TARGET_HAS_bswap32_i32;
    case INDEX_op_not_i32:
        return TCG_TARGET_HAS_not_i32;
    case INDEX_op_neg_i32:
        return TCG_TARGET_HAS_neg_i32;
    case INDEX_op_andc_i32:
        return TCG_TARGET_HAS_andc_i32;
    case INDEX_op_orc_i32:
        return TCG_TARGET_HAS_orc_i32;
    case INDEX_op_eqv_i32:
        return TCG_TARGET_HAS_eqv_i32;
    case INDEX_op_nand_i32:
        return TCG_TARGET_HAS_nand_i32;
    case INDEX_op_nor_i32:
        return TCG_TARGET_HAS_nor_i32;
    case INDEX_op_clz_i32:
        return TCG_TARGET_HAS_clz_i32;
    case INDEX_op_ctz_i32:
        return TCG_TARGET_HAS_ctz_i32;
    case INDEX_op_ctpop_i32:
        return TCG_TARGET_HAS_ctpop_i32;

    case INDEX_op_brcond2_i32:
    case INDEX_op_setcond2_i32:
        return TCG_TARGET_REG_BITS == 32;

    case INDEX_op_setcond_i64:
    case INDEX_op_brcond_i64:
    case INDEX_op_ld8u_i64:
    case INDEX_op_ld8s_i64:
    case INDEX_op_ld16u_i64:
    case INDEX_op_ld16s_i64:
    case INDEX_op_ld32u_i64:
    case INDEX_op_ld32s_i64:
    case INDEX_op_ld_i64:
    case INDEX_op_st8_i64:
    case INDEX_op_st16_i64:
    case INDEX_op_st32_i64:
    case INDEX_op_st_i64:
    case INDEX_op_add_i64:
    case INDEX_op_sub_i64:
    case INDEX_op_mul_i64:
    case INDEX_op_and_i64:
    case INDEX_op_or_i64:
    case INDEX_op_xor_i64:
    case INDEX_op_shl_i64:
    case INDEX_op_shr_i64:
    case INDEX_op_sar_i64:
    case INDEX_op_ext_i32_i64:
    case INDEX_op_extu_i32_i64:
    case INDEX_op_tlb_load:
    case INDEX_op_tlb_guard:
    case INDEX_op_itlb_load:
    case INDEX_op_tlb_check:
    case INDEX_op_itlb_check:
    /* Yes, we just won't support 32-bit hosts.  */
    case INDEX_op_brcond_guard_i32:
    case INDEX_op_brcond_guard_i64:
        return TCG_TARGET_REG_BITS == 64;

    case INDEX_op_movcond_i64:
        return TCG_TARGET_HAS_movcond_i64;
    case INDEX_op_div_i64:
    case INDEX_op_divu_i64:
        return TCG_TARGET_HAS_div_i64;
    case INDEX_op_rem_i64:
    case INDEX_op_remu_i64:
        return TCG_TARGET_HAS_rem_i64;
    case INDEX_op_div2_i64:
    case INDEX_op_divu2_i64:
        return TCG_TARGET_HAS_div2_i64;
    case INDEX_op_rotl_i64:
    case INDEX_op_rotr_i64:
        return TCG_TARGET_HAS_rot_i64;
    case INDEX_op_deposit_i64:
        return TCG_TARGET_HAS_deposit_i64;
    case INDEX_op_extract_i64:
        return TCG_TARGET_HAS_extract_i64;
    case INDEX_op_sextract_i64:
        return TCG_TARGET_HAS_sextract_i64;
    case INDEX_op_extract2_i64:
        return TCG_TARGET_HAS_extract2_i64;
    case INDEX_op_extrl_i64_i32:
        return TCG_TARGET_HAS_extrl_i64_i32;
    case INDEX_op_extrh_i64_i32:
        return TCG_TARGET_HAS_extrh_i64_i32;
    case INDEX_op_ext8s_i64:
        return TCG_TARGET_HAS_ext8s_i64;
    case INDEX_op_ext16s_i64:
        return TCG_TARGET_HAS_ext16s_i64;
    case INDEX_op_ext32s_i64:
        return TCG_TARGET_HAS_ext32s_i64;
    case INDEX_op_ext8u_i64:
        return TCG_TARGET_HAS_ext8u_i64;
    case INDEX_op_ext16u_i64:
        return TCG_TARGET_HAS_ext16u_i64;
    case INDEX_op_ext32u_i64:
        return TCG_TARGET_HAS_ext32u_i64;
    case INDEX_op_bswap16_i64:
        return TCG_TARGET_HAS_bswap16_i64;
    case INDEX_op_bswap32_i64:
        return TCG_TARGET_HAS_bswap32_i64;
    case INDEX_op_bswap64_i64:
        return TCG_TARGET_HAS_bswap64_i64;
    case INDEX_op_not_i64:
        return TCG_TARGET_HAS_not_i64;
    case INDEX_op_neg_i64:
        return TCG_TARGET_HAS_neg_i64;
    case INDEX_op_andc_i64:
        return TCG_TARGET_HAS_andc_i64;
    case INDEX_op_orc_i64:
        return TCG_TARGET_HAS_orc_i64;
    case INDEX_op_eqv_i64:
        return TCG_TARGET_HAS_eqv_i64;
    case INDEX_op_nand_i64:
        return TCG_TARGET_HAS_nand_i64;
    case INDEX_op_nor_i64:
        return TCG_TARGET_HAS_nor_i64;
    case INDEX_op_clz_i64:
        return TCG_TARGET_HAS_clz_i64;
    case INDEX_op_ctz_i64:
        return TCG_TARGET_HAS_ctz_i64;
    case INDEX_op_ctpop_i64:
        return TCG_TARGET_HAS_ctpop_i64;
    case INDEX_op_add2_i64:
        return TCG_TARGET_HAS_add2_i64;
    case INDEX_op_sub2_i64:
        return TCG_TARGET_HAS_sub2_i64;
    case INDEX_op_mulu2_i64:
        return TCG_TARGET_HAS_mulu2_i64;
    case INDEX_op_muls2_i64:
        return TCG_TARGET_HAS_muls2_i64;
    case INDEX_op_muluh_i64:
        return TCG_TARGET_HAS_muluh_i64;
    case INDEX_op_mulsh_i64:
        return TCG_TARGET_HAS_mulsh_i64;

    case INDEX_op_dupm_vec:
    case INDEX_op_ld_vec:
    case INDEX_op_st_vec:
    case INDEX_op_add_vec:
    case INDEX_op_sub_vec:
    case INDEX_op_and_vec:
    case INDEX_op_or_vec:
    case INDEX_op_xor_vec:
    case INDEX_op_cmp_vec:
        return have_vec;
    case INDEX_op_dup2_vec:
        return have_vec && TCG_TARGET_REG_BITS == 32;
    case INDEX_op_not_vec:
        return have_vec && TCG_TARGET_HAS_not_vec;
    case INDEX_op_neg_vec:
        return have_vec && TCG_TARGET_HAS_neg_vec;
    case INDEX_op_abs_vec:
        return have_vec && TCG_TARGET_HAS_abs_vec;
    case INDEX_op_andc_vec:
        return have_vec && TCG_TARGET_HAS_andc_vec;
    case INDEX_op_orc_vec:
        return have_vec && TCG_TARGET_HAS_orc_vec;
    case INDEX_op_mul_vec:
        return have_vec && TCG_TARGET_HAS_mul_vec;
    case INDEX_op_shli_vec:
    case INDEX_op_shri_vec:
    case INDEX_op_sari_vec:
        return have_vec && TCG_TARGET_HAS_shi_vec;
    case INDEX_op_shls_vec:
    case INDEX_op_shrs_vec:
    case INDEX_op_sars_vec:
        return have_vec && TCG_TARGET_HAS_shs_vec;
    case INDEX_op_shlv_vec:
    case INDEX_op_shrv_vec:
    case INDEX_op_sarv_vec:
        return have_vec && TCG_TARGET_HAS_shv_vec;
    case INDEX_op_rotli_vec:
        return have_vec && TCG_TARGET_HAS_roti_vec;
    case INDEX_op_rotls_vec:
        return have_vec && TCG_TARGET_HAS_rots_vec;
    case INDEX_op_rotlv_vec:
    case INDEX_op_rotrv_vec:
        return have_vec && TCG_TARGET_HAS_rotv_vec;
    case INDEX_op_ssadd_vec:
    case INDEX_op_usadd_vec:
    case INDEX_op_sssub_vec:
    case INDEX_op_ussub_vec:
        return have_vec && TCG_TARGET_HAS_sat_vec;
    case INDEX_op_smin_vec:
    case INDEX_op_umin_vec:
    case INDEX_op_smax_vec:
    case INDEX_op_umax_vec:
        return have_vec && TCG_TARGET_HAS_minmax_vec;
    case INDEX_op_bitsel_vec:
        return have_vec && TCG_TARGET_HAS_bitsel_vec;
    case INDEX_op_cmpsel_vec:
        return have_vec && TCG_TARGET_HAS_cmpsel_vec;

    default:
        tcg_debug_assert(op > INDEX_op_last_generic && op < NB_OPS);
        return true;
    }
}

/* Note: we convert the 64 bit args to 32 bit and do some alignment
   and endian swap. Maybe it would be better to do the alignment
   and endian swap in tcg_reg_alloc_call(). */
void tcg_gen_callN(void *func, TCGTemp *ret, int nargs, TCGTemp **args)
{
    int i, real_args, nb_rets, pi;
    unsigned sizemask, flags;
    TCGHelperInfo *info;
    TCGOp *op;

    info = g_hash_table_lookup(helper_table, (gpointer)func);
    flags = info->flags;
    sizemask = info->sizemask;

#ifdef CONFIG_PLUGIN
    /* detect non-plugin helpers */
    if (tcg_ctx->plugin_insn && unlikely(strncmp(info->name, "plugin_", 7))) {
        tcg_ctx->plugin_insn->calls_helpers = true;
    }
#endif

#if defined(__sparc__) && !defined(__arch64__) \
    && !defined(CONFIG_TCG_INTERPRETER)
    /* We have 64-bit values in one register, but need to pass as two
       separate parameters.  Split them.  */
    int orig_sizemask = sizemask;
    int orig_nargs = nargs;
    TCGv_i64 retl, reth;
    TCGTemp *split_args[MAX_OPC_PARAM];

    retl = NULL;
    reth = NULL;
    if (sizemask != 0) {
        for (i = real_args = 0; i < nargs; ++i) {
            int is_64bit = sizemask & (1 << (i+1)*2);
            if (is_64bit) {
                TCGv_i64 orig = temp_tcgv_i64(args[i]);
                TCGv_i32 h = tcg_temp_new_i32();
                TCGv_i32 l = tcg_temp_new_i32();
                tcg_gen_extr_i64_i32(l, h, orig);
                split_args[real_args++] = tcgv_i32_temp(h);
                split_args[real_args++] = tcgv_i32_temp(l);
            } else {
                split_args[real_args++] = args[i];
            }
        }
        nargs = real_args;
        args = split_args;
        sizemask = 0;
    }
#elif defined(TCG_TARGET_EXTEND_ARGS) && TCG_TARGET_REG_BITS == 64
    for (i = 0; i < nargs; ++i) {
        int is_64bit = sizemask & (1 << (i+1)*2);
        int is_signed = sizemask & (2 << (i+1)*2);
        if (!is_64bit) {
            TCGv_i64 temp = tcg_temp_new_i64();
            TCGv_i64 orig = temp_tcgv_i64(args[i]);
            if (is_signed) {
                tcg_gen_ext32s_i64(temp, orig);
            } else {
                tcg_gen_ext32u_i64(temp, orig);
            }
            args[i] = tcgv_i64_temp(temp);
        }
    }
#endif /* TCG_TARGET_EXTEND_ARGS */

    op = tcg_emit_op(INDEX_op_call);

    pi = 0;
    if (ret != NULL) {
#if defined(__sparc__) && !defined(__arch64__) \
    && !defined(CONFIG_TCG_INTERPRETER)
        if (orig_sizemask & 1) {
            /* The 32-bit ABI is going to return the 64-bit value in
               the %o0/%o1 register pair.  Prepare for this by using
               two return temporaries, and reassemble below.  */
            retl = tcg_temp_new_i64();
            reth = tcg_temp_new_i64();
            op->args[pi++] = tcgv_i64_arg(reth);
            op->args[pi++] = tcgv_i64_arg(retl);
            nb_rets = 2;
        } else {
            op->args[pi++] = temp_arg(ret);
            nb_rets = 1;
        }
#else
        if (TCG_TARGET_REG_BITS < 64 && (sizemask & 1)) {
#ifdef HOST_WORDS_BIGENDIAN
            op->args[pi++] = temp_arg(ret + 1);
            op->args[pi++] = temp_arg(ret);
#else
            op->args[pi++] = temp_arg(ret);
            op->args[pi++] = temp_arg(ret + 1);
#endif
            nb_rets = 2;
        } else {
            op->args[pi++] = temp_arg(ret);
            nb_rets = 1;
        }
#endif
    } else {
        nb_rets = 0;
    }
    TCGOP_CALLO(op) = nb_rets;

    real_args = 0;
    for (i = 0; i < nargs; i++) {
        int is_64bit = sizemask & (1 << (i+1)*2);
        if (TCG_TARGET_REG_BITS < 64 && is_64bit) {
#ifdef TCG_TARGET_CALL_ALIGN_ARGS
            /* some targets want aligned 64 bit args */
            if (real_args & 1) {
                op->args[pi++] = TCG_CALL_DUMMY_ARG;
                real_args++;
            }
#endif
           /* If stack grows up, then we will be placing successive
              arguments at lower addresses, which means we need to
              reverse the order compared to how we would normally
              treat either big or little-endian.  For those arguments
              that will wind up in registers, this still works for
              HPPA (the only current STACK_GROWSUP target) since the
              argument registers are *also* allocated in decreasing
              order.  If another such target is added, this logic may
              have to get more complicated to differentiate between
              stack arguments and register arguments.  */
#if defined(HOST_WORDS_BIGENDIAN) != defined(TCG_TARGET_STACK_GROWSUP)
            op->args[pi++] = temp_arg(args[i] + 1);
            op->args[pi++] = temp_arg(args[i]);
#else
            op->args[pi++] = temp_arg(args[i]);
            op->args[pi++] = temp_arg(args[i] + 1);
#endif
            real_args += 2;
            continue;
        }

        op->args[pi++] = temp_arg(args[i]);
        real_args++;
    }
    op->args[pi++] = (uintptr_t)func;
    op->args[pi++] = flags;
    TCGOP_CALLI(op) = real_args;

    /* Make sure the fields didn't overflow.  */
    tcg_debug_assert(TCGOP_CALLI(op) == real_args);
    tcg_debug_assert(pi <= ARRAY_SIZE(op->args));

#if defined(__sparc__) && !defined(__arch64__) \
    && !defined(CONFIG_TCG_INTERPRETER)
    /* Free all of the parts we allocated above.  */
    for (i = real_args = 0; i < orig_nargs; ++i) {
        int is_64bit = orig_sizemask & (1 << (i+1)*2);
        if (is_64bit) {
            tcg_temp_free_internal(args[real_args++]);
            tcg_temp_free_internal(args[real_args++]);
        } else {
            real_args++;
        }
    }
    if (orig_sizemask & 1) {
        /* The 32-bit ABI returned two 32-bit pieces.  Re-assemble them.
           Note that describing these as TCGv_i64 eliminates an unnecessary
           zero-extension that tcg_gen_concat_i32_i64 would create.  */
        tcg_gen_concat32_i64(temp_tcgv_i64(ret), retl, reth);
        tcg_temp_free_i64(retl);
        tcg_temp_free_i64(reth);
    }
#elif defined(TCG_TARGET_EXTEND_ARGS) && TCG_TARGET_REG_BITS == 64
    for (i = 0; i < nargs; ++i) {
        int is_64bit = sizemask & (1 << (i+1)*2);
        if (!is_64bit) {
            tcg_temp_free_internal(args[i]);
        }
    }
#endif /* TCG_TARGET_EXTEND_ARGS */
}

static char *tcg_get_arg_str_ptr(TCGContext *s, char *buf, int buf_size,
                                 TCGTemp *ts)
{
    int idx = temp_idx(ts);

    switch (ts->kind) {
    case TEMP_FIXED:
    case TEMP_GLOBAL:
        pstrcpy(buf, buf_size, ts->name);
        break;
    case TEMP_LOCAL:
        snprintf(buf, buf_size, "loc%d", idx - s->nb_globals);
        break;
    case TEMP_NORMAL:
        snprintf(buf, buf_size, "tmp%d", idx - s->nb_globals);
        break;
    case TEMP_CONST:
        switch (ts->type) {
        case TCG_TYPE_I32:
            snprintf(buf, buf_size, "$0x%x", (int32_t)ts->val);
            break;
#if TCG_TARGET_REG_BITS > 32
        case TCG_TYPE_I64:
            snprintf(buf, buf_size, "$0x%" PRIx64, ts->val);
            break;
#endif
        case TCG_TYPE_V64:
        case TCG_TYPE_V128:
        case TCG_TYPE_V256:
            snprintf(buf, buf_size, "v%d$0x%" PRIx64,
                     64 << (ts->type - TCG_TYPE_V64), ts->val);
            break;
        default:
            g_assert_not_reached();
        }
        break;
    }
    return buf;
}

static char *tcg_get_arg_str(TCGContext *s, char *buf,
                             int buf_size, TCGArg arg)
{
    return tcg_get_arg_str_ptr(s, buf, buf_size, arg_temp(arg));
}

/* Find helper name.  */
static inline const char *tcg_find_helper(TCGContext *s, uintptr_t val)
{
    const char *ret = NULL;
    if (helper_table) {
        TCGHelperInfo *info = g_hash_table_lookup(helper_table, (gpointer)val);
        if (info) {
            ret = info->name;
        }
    }
    return ret;
}

static const char * const cond_name[] =
{
    [TCG_COND_NEVER] = "never",
    [TCG_COND_ALWAYS] = "always",
    [TCG_COND_EQ] = "eq",
    [TCG_COND_NE] = "ne",
    [TCG_COND_LT] = "lt",
    [TCG_COND_GE] = "ge",
    [TCG_COND_LE] = "le",
    [TCG_COND_GT] = "gt",
    [TCG_COND_LTU] = "ltu",
    [TCG_COND_GEU] = "geu",
    [TCG_COND_LEU] = "leu",
    [TCG_COND_GTU] = "gtu"
};

static const char * const ldst_name[] =
{
    [MO_UB]   = "ub",
    [MO_SB]   = "sb",
    [MO_LEUW] = "leuw",
    [MO_LESW] = "lesw",
    [MO_LEUL] = "leul",
    [MO_LESL] = "lesl",
    [MO_LEQ]  = "leq",
    [MO_BEUW] = "beuw",
    [MO_BESW] = "besw",
    [MO_BEUL] = "beul",
    [MO_BESL] = "besl",
    [MO_BEQ]  = "beq",
};

static const char * const alignment_name[(MO_AMASK >> MO_ASHIFT) + 1] = {
#ifdef TARGET_ALIGNED_ONLY
    [MO_UNALN >> MO_ASHIFT]    = "un+",
    [MO_ALIGN >> MO_ASHIFT]    = "",
#else
    [MO_UNALN >> MO_ASHIFT]    = "",
    [MO_ALIGN >> MO_ASHIFT]    = "al+",
#endif
    [MO_ALIGN_2 >> MO_ASHIFT]  = "al2+",
    [MO_ALIGN_4 >> MO_ASHIFT]  = "al4+",
    [MO_ALIGN_8 >> MO_ASHIFT]  = "al8+",
    [MO_ALIGN_16 >> MO_ASHIFT] = "al16+",
    [MO_ALIGN_32 >> MO_ASHIFT] = "al32+",
    [MO_ALIGN_64 >> MO_ASHIFT] = "al64+",
};

static inline bool tcg_regset_single(TCGRegSet d)
{
    return (d & (d - 1)) == 0;
}

static inline TCGReg tcg_regset_first(TCGRegSet d)
{
    if (TCG_TARGET_NB_REGS <= 32) {
        return ctz32(d);
    } else {
        return ctz64(d);
    }
}

static void tcg_dump_ops(TCGContext *s, bool have_prefs)
{
    char buf[128];
    TCGOp *op;

    QTAILQ_FOREACH(op, &s->ops, link) {
        int i, k, nb_oargs, nb_iargs, nb_cargs;
        const TCGOpDef *def;
        TCGOpcode c;
        int col = 0;

        c = op->opc;
        def = &tcg_op_defs[c];

        if (c == INDEX_op_insn_start) {
            nb_oargs = 0;
            col += qemu_log("\n ----");

            for (i = 0; i < TARGET_INSN_START_WORDS; ++i) {
                target_ulong a;
#if TARGET_LONG_BITS > TCG_TARGET_REG_BITS
                a = deposit64(op->args[i * 2], 32, 32, op->args[i * 2 + 1]);
#else
                a = op->args[i];
#endif
                col += qemu_log(" " TARGET_FMT_lx, a);
            }
        } else if (c == INDEX_op_call) {
            /* variable number of arguments */
            nb_oargs = TCGOP_CALLO(op);
            nb_iargs = TCGOP_CALLI(op);
            nb_cargs = def->nb_cargs;

            /* function name, flags, out args */
            col += qemu_log(" %s %s,$0x%" TCG_PRIlx ",$%d", def->name,
                            tcg_find_helper(s, op->args[nb_oargs + nb_iargs]),
                            op->args[nb_oargs + nb_iargs + 1], nb_oargs);
            for (i = 0; i < nb_oargs; i++) {
                col += qemu_log(",%s", tcg_get_arg_str(s, buf, sizeof(buf),
                                                       op->args[i]));
            }
            for (i = 0; i < nb_iargs; i++) {
                TCGArg arg = op->args[nb_oargs + i];
                const char *t = "<dummy>";
                if (arg != TCG_CALL_DUMMY_ARG) {
                    t = tcg_get_arg_str(s, buf, sizeof(buf), arg);
                }
                col += qemu_log(",%s", t);
            }
        } else {
            col += qemu_log(" %s ", def->name);

            nb_oargs = def->nb_oargs;
            nb_iargs = def->nb_iargs;
            nb_cargs = def->nb_cargs;

            if (def->flags & TCG_OPF_VECTOR) {
                col += qemu_log("v%d,e%d,", 64 << TCGOP_VECL(op),
                                8 << TCGOP_VECE(op));
            }

            k = 0;
            for (i = 0; i < nb_oargs; i++) {
                if (k != 0) {
                    col += qemu_log(",");
                }
                col += qemu_log("%s", tcg_get_arg_str(s, buf, sizeof(buf),
                                                      op->args[k++]));
            }
            for (i = 0; i < nb_iargs; i++) {
                if (k != 0) {
                    col += qemu_log(",");
                }
                col += qemu_log("%s", tcg_get_arg_str(s, buf, sizeof(buf),
                                                      op->args[k++]));
            }
            switch (c) {
            case INDEX_op_brcond_i32:
            case INDEX_op_setcond_i32:
            case INDEX_op_movcond_i32:
            case INDEX_op_brcond2_i32:
            case INDEX_op_setcond2_i32:
            case INDEX_op_brcond_i64:
            case INDEX_op_setcond_i64:
            case INDEX_op_movcond_i64:
            case INDEX_op_cmp_vec:
            case INDEX_op_cmpsel_vec:
                if (op->args[k] < ARRAY_SIZE(cond_name)
                    && cond_name[op->args[k]]) {
                    col += qemu_log(",%s", cond_name[op->args[k++]]);
                } else {
                    col += qemu_log(",$0x%" TCG_PRIlx, op->args[k++]);
                }
                i = 1;
                break;
            case INDEX_op_qemu_ld_i32:
            case INDEX_op_qemu_st_i32:
            case INDEX_op_qemu_ld_i64:
            case INDEX_op_qemu_st_i64:
                {
                    TCGMemOpIdx oi = op->args[k++];
                    MemOp op = get_memop(oi);
                    unsigned ix = get_mmuidx(oi);

                    if (op & ~(MO_AMASK | MO_BSWAP | MO_SSIZE)) {
                        col += qemu_log(",$0x%x,%u", op, ix);
                    } else {
                        const char *s_al, *s_op;
                        s_al = alignment_name[(op & MO_AMASK) >> MO_ASHIFT];
                        s_op = ldst_name[op & (MO_BSWAP | MO_SSIZE)];
                        col += qemu_log(",%s%s,%u", s_al, s_op, ix);
                    }
                    i = 1;
                }
                break;
            default:
                i = 0;
                break;
            }
            switch (c) {
            case INDEX_op_set_label:
            case INDEX_op_br:
            case INDEX_op_brcond_i32:
            case INDEX_op_brcond_i64:
            case INDEX_op_brcond2_i32:
                col += qemu_log("%s$L%d", k ? "," : "",
                                arg_label(op->args[k])->id);
                i++, k++;
                break;
            default:
                break;
            }
            for (; i < nb_cargs; i++, k++) {
                col += qemu_log("%s$0x%" TCG_PRIlx, k ? "," : "", op->args[k]);
            }
        }

        if (have_prefs || op->life) {

            QemuLogFile *logfile;

            rcu_read_lock();
            logfile = qatomic_rcu_read(&qemu_logfile);
            if (logfile) {
                for (; col < 40; ++col) {
                    putc(' ', logfile->fd);
                }
            }
            rcu_read_unlock();
        }

        if (op->life) {
            unsigned life = op->life;
            uint32_t mask;

            if (life & (DEAD_ARG - SYNC_ARG)) {
                qemu_log("  sync:");
                for (i = 0, mask = SYNC_ARG; mask < DEAD_ARG; mask <<= 1, i++) {
                    if (life & mask) {
                        qemu_log(" %d", i);
                    }
                }
            }
            if (life & (CLOBBER_ARG - DEAD_ARG)) {
                qemu_log("  dead:");
                for (i = 0, mask = DEAD_ARG; mask < CLOBBER_ARG;
                     mask <<= 1, i++) {
                    if (life & mask) {
                        qemu_log(" %d", i);
                    }
                }
            }
            if (life & (0 - CLOBBER_ARG)) {
                qemu_log("  may clobber:");
                for (i = 0, mask = CLOBBER_ARG; mask < (TCGLifeData) -1;
                     mask <<= 1, i++) {
                    if (life & mask) {
                        qemu_log(" %d", i);
                    }
                }
            }
        }

        if (have_prefs) {
            for (i = 0; i < nb_oargs; ++i) {
                TCGRegSet set = op->output_pref[i];

                if (i == 0) {
                    qemu_log("  pref=");
                } else {
                    qemu_log(",");
                }
                if (set == 0) {
                    qemu_log("none");
                } else if (set == MAKE_64BIT_MASK(0, TCG_TARGET_NB_REGS)) {
                    qemu_log("all");
#ifdef CONFIG_DEBUG_TCG
                } else if (tcg_regset_single(set)) {
                    TCGReg reg = tcg_regset_first(set);
                    qemu_log("%s", tcg_target_reg_names[reg]);
#endif
                } else if (TCG_TARGET_NB_REGS <= 32) {
                    qemu_log("%#x", (uint32_t)set);
                } else {
                    qemu_log("%#" PRIx64, (uint64_t)set);
                }
            }
        }

        qemu_log("\n");
    }
}

/* we give more priority to constraints with less registers */
static int get_constraint_priority(const TCGOpDef *def, int k)
{
    const TCGArgConstraint *arg_ct = &def->args_ct[k];
    int n;

    if (arg_ct->oalias) {
        /* an alias is equivalent to a single register */
        n = 1;
    } else {
        n = ctpop64(arg_ct->regs);
    }
    return TCG_TARGET_NB_REGS - n + 1;
}

/* sort from highest priority to lowest */
static void sort_constraints(TCGOpDef *def, int start, int n)
{
    int i, j;
    TCGArgConstraint *a = def->args_ct;

    for (i = 0; i < n; i++) {
        a[start + i].sort_index = start + i;
    }
    if (n <= 1) {
        return;
    }
    for (i = 0; i < n - 1; i++) {
        for (j = i + 1; j < n; j++) {
            int p1 = get_constraint_priority(def, a[start + i].sort_index);
            int p2 = get_constraint_priority(def, a[start + j].sort_index);
            if (p1 < p2) {
                int tmp = a[start + i].sort_index;
                a[start + i].sort_index = a[start + j].sort_index;
                a[start + j].sort_index = tmp;
            }
        }
    }
}

static void process_op_defs(TCGContext *s)
{
    TCGOpcode op;

    for (op = 0; op < NB_OPS; op++) {
        TCGOpDef *def = &tcg_op_defs[op];
        const TCGTargetOpDef *tdefs;
        TCGType type;
        int i, nb_args;

        if (def->flags & TCG_OPF_NOT_PRESENT) {
            continue;
        }

        nb_args = def->nb_iargs + def->nb_oargs;
        if (nb_args == 0) {
            continue;
        }

        tdefs = tcg_target_op_def(op);
        /* Missing TCGTargetOpDef entry. */
        tcg_debug_assert(tdefs != NULL);

        type = (def->flags & TCG_OPF_64BIT ? TCG_TYPE_I64 : TCG_TYPE_I32);
        for (i = 0; i < nb_args; i++) {
            const char *ct_str = tdefs->args_ct_str[i];
            /* Incomplete TCGTargetOpDef entry. */
            tcg_debug_assert(ct_str != NULL);

            while (*ct_str != '\0') {
                switch(*ct_str) {
                case '0' ... '9':
                    {
                        int oarg = *ct_str - '0';
                        tcg_debug_assert(ct_str == tdefs->args_ct_str[i]);
                        tcg_debug_assert(oarg < def->nb_oargs);
                        tcg_debug_assert(def->args_ct[oarg].regs != 0);
                        def->args_ct[i] = def->args_ct[oarg];
                        /* The output sets oalias.  */
                        def->args_ct[oarg].oalias = true;
                        def->args_ct[oarg].alias_index = i;
                        /* The input sets ialias. */
                        def->args_ct[i].ialias = true;
                        def->args_ct[i].alias_index = oarg;
                    }
                    ct_str++;
                    break;
                case '&':
                    def->args_ct[i].newreg = true;
                    ct_str++;
                    break;
                case 'i':
                    def->args_ct[i].ct |= TCG_CT_CONST;
                    ct_str++;
                    break;
                default:
                    ct_str = target_parse_constraint(&def->args_ct[i],
                                                     ct_str, type);
                    /* Typo in TCGTargetOpDef constraint. */
                    tcg_debug_assert(ct_str != NULL);
                }
            }
        }

        /* TCGTargetOpDef entry with too much information? */
        tcg_debug_assert(i == TCG_MAX_OP_ARGS || tdefs->args_ct_str[i] == NULL);

        /* sort the constraints (XXX: this is just an heuristic) */
        sort_constraints(def, 0, def->nb_oargs);
        sort_constraints(def, def->nb_oargs, def->nb_iargs);
    }
}

void tcg_op_remove(TCGContext *s, TCGOp *op)
{
    TCGLabel *label;

    switch (op->opc) {
    case INDEX_op_br:
        label = arg_label(op->args[0]);
        label->refs--;
        break;
    case INDEX_op_brcond_i32:
    case INDEX_op_brcond_i64:
        label = arg_label(op->args[3]);
        label->refs--;
        break;
    case INDEX_op_brcond2_i32:
        label = arg_label(op->args[5]);
        label->refs--;
        break;
    default:
        break;
    }

    QTAILQ_REMOVE(&s->ops, op, link);
    QTAILQ_INSERT_TAIL(&s->free_ops, op, link);
    s->nb_ops--;

#ifdef CONFIG_PROFILER
    qatomic_set(&s->prof.del_op_count, s->prof.del_op_count + 1);
#endif
}

static TCGOp *tcg_op_alloc(TCGOpcode opc)
{
    TCGContext *s = tcg_ctx;
    TCGOp *op;

    if (likely(QTAILQ_EMPTY(&s->free_ops))) {
        op = tcg_malloc(sizeof(TCGOp));
    } else {
        op = QTAILQ_FIRST(&s->free_ops);
        QTAILQ_REMOVE(&s->free_ops, op, link);
    }
    memset(op, 0, offsetof(TCGOp, link));
    op->opc = opc;
    s->nb_ops++;

    return op;
}

TCGOp *tcg_emit_op(TCGOpcode opc)
{
    TCGOp *op = tcg_op_alloc(opc);
    QTAILQ_INSERT_TAIL(&tcg_ctx->ops, op, link);
    return op;
}

TCGOp *tcg_op_insert_before(TCGContext *s, TCGOp *old_op, TCGOpcode opc)
{
    TCGOp *new_op = tcg_op_alloc(opc);
    QTAILQ_INSERT_BEFORE(old_op, new_op, link);
    return new_op;
}

TCGOp *tcg_op_insert_after(TCGContext *s, TCGOp *old_op, TCGOpcode opc)
{
    TCGOp *new_op = tcg_op_alloc(opc);
    QTAILQ_INSERT_AFTER(&s->ops, old_op, new_op, link);
    return new_op;
}

/* Reachable analysis : remove unreachable code.  */
static void reachable_code_pass(TCGContext *s)
{
    TCGOp *op, *op_next;
    bool dead = false;

    QTAILQ_FOREACH_SAFE(op, &s->ops, link, op_next) {
        bool remove = dead;
        TCGLabel *label;
        uint16_t call_flags;

        switch (op->opc) {
        case INDEX_op_set_label:
            label = arg_label(op->args[0]);
            if (label->refs == 0) {
                /*
                 * While there is an occasional backward branch, virtually
                 * all branches generated by the translators are forward.
                 * Which means that generally we will have already removed
                 * all references to the label that will be, and there is
                 * little to be gained by iterating.
                 */
                remove = true;
            } else {
                /* Once we see a label, insns become live again.  */
                dead = false;
                remove = false;

                /*
                 * Optimization can fold conditional branches to unconditional.
                 * If we find a label with one reference which is preceded by
                 * an unconditional branch to it, remove both.  This needed to
                 * wait until the dead code in between them was removed.
                 */
                if (label->refs == 1) {
                    TCGOp *op_prev = QTAILQ_PREV(op, link);
                    if (op_prev->opc == INDEX_op_br &&
                        label == arg_label(op_prev->args[0])) {
                        tcg_op_remove(s, op_prev);
                        remove = true;
                    }
                }
            }
            break;

        case INDEX_op_br:
        case INDEX_op_exit_tb:
        case INDEX_op_goto_ptr:
            /* Unconditional branches; everything following is dead.  */
            dead = true;
            break;

        case INDEX_op_call:
            /* Notice noreturn helper calls, raising exceptions.  */
            call_flags = op->args[TCGOP_CALLO(op) + TCGOP_CALLI(op) + 1];
            if (call_flags & TCG_CALL_NO_RETURN) {
                dead = true;
            }
            break;

        case INDEX_op_insn_start:
            /* Never remove -- we need to keep these for unwind.  */
            remove = false;
            break;

        default:
            break;
        }

        if (remove) {
            tcg_op_remove(s, op);
        }
    }
}

/*
 * TCG liveness analysis facilities
 */

#define TS_DEAD                 (1 << 0)
#define TS_MAY_CLOBBER          (1 << 1)
#define TS_SYNC                 (1 << 2)

#define IS_DEAD_ARG(n)          (op->life & (DEAD_ARG << (n)))
#define MAY_CLOBBER_ARG(n)      (op->life & (CLOBBER_ARG << (n)))
#define NEED_SYNC_ARG(n)        (op->life & (SYNC_ARG << (n)))

typedef struct TempLivenessInfo {
    TCGRegSet preferred_regs;
    uint16_t next_use;
} TempLivenessInfo;

static inline TempLivenessInfo *la_info(const TCGTemp *ts)
{
    return ts->state_ptr;
}

static inline uint16_t la_next_use(const TCGTemp *ts)
{
    return ts->state & TS_DEAD ? tcg_ctx->current_insn
                               : la_info(ts)->next_use;
}

static inline void la_set_next_use(TCGTemp *ts, uint16_t next_use)
{
    la_info(ts)->next_use = next_use;
}

/* For liveness_pass_1, the register preferences for a given temp.  */
static inline TCGRegSet *la_temp_pref(TCGTemp *ts)
{
    return &la_info(ts)->preferred_regs;
}

/* For liveness_pass_1, reset the preferences for a given temp to the
 * maximal regset for its type.  */
static inline void la_reset_pref(TCGTemp *ts)
{
    *la_temp_pref(ts)
        = (ts->state == TS_DEAD ? 0 : tcg_target_available_regs[ts->type]);
}

/* Liveness analysis: sync globals back to memory and kill.  */
static void la_global_kill(TCGContext *s, size_t ng)
{
    for (size_t i = 0; i < ng; i++) {
        s->temps[i].state = TS_DEAD | TS_SYNC;
        la_reset_pref(&s->temps[i]);
    }
}

/* Liveness analysis: end of function: all temps are dead, and globals
 * should be in memory.  */
static void la_func_end(TCGContext *s, size_t ng, size_t nt)
{
    la_global_kill(s, ng);

    for (size_t i = ng; i < nt; ++i) {
        s->temps[i].state = TS_DEAD;
        la_reset_pref(&s->temps[i]);
    }
}

/* Liveness analysis: end of basic block: all temps are dead, globals
 * and local temps should be in memory.  */
static void la_bb_end(TCGContext *s, size_t ng, size_t nt)
{
    la_global_kill(s, ng);

    for (size_t i = ng; i < nt; ++i) {
        TCGTemp *ts = &s->temps[i];
        uint32_t state;

        switch (ts->kind) {
        case TEMP_LOCAL:
            state = TS_DEAD | TS_SYNC;
            break;
        case TEMP_NORMAL:
        case TEMP_CONST:
            state = TS_DEAD;
            break;
        default:
            g_assert_not_reached();
        }
        ts->state = state;
        la_reset_pref(ts);
    }
}

/* Liveness analysis: sync globals back to memory.  */
static void la_global_sync(TCGContext *s, size_t ng)
{
    for (size_t i = 0; i < ng; ++i) {
        uint32_t state = s->temps[i].state;

        s->temps[i].state = state | TS_SYNC;
        if (state == TS_DEAD) {
            /* If the global was previously dead, reset prefs.  */
            la_reset_pref(&s->temps[i]);
        }
    }
}

/*
 * Liveness analysis: conditional branch: all temps are dead,
 * globals and local temps should be synced.
 */
static void la_bb_sync(TCGContext *s, size_t ng, size_t nt)
{
    la_global_sync(s, ng);

    for (size_t i = ng; i < nt; ++i) {
        TCGTemp *ts = &s->temps[i];
        uint32_t state;

        switch (ts->kind) {
        case TEMP_LOCAL:
            state = ts->state;
            ts->state = state | TS_SYNC;
            if (state != TS_DEAD) {
                continue;
            }
            break;
        case TEMP_NORMAL:
            s->temps[i].state = TS_DEAD;
            break;
        case TEMP_CONST:
            continue;
        default:
            g_assert_not_reached();
        }
        la_reset_pref(&s->temps[i]);
    }
}

/* Liveness analysis: note live globals crossing calls.  */
static void la_cross_call(TCGContext *s, size_t nt, bool tlb_check)
{
    TCGRegSet mask = ~(tlb_check ? tcg_target_tlb_check_clobber_regs
                                 : tcg_target_call_clobber_regs);

    for (size_t i = 0; i < nt; i++) {
        TCGTemp *ts = &s->temps[i];

        if (!(ts->state & TS_DEAD)) {
            TCGRegSet *pset = la_temp_pref(ts);
            TCGRegSet set = *pset;

            set &= mask;
            /* If the combination is not possible, restart.  */
            if (set == 0) {
                set = tcg_target_available_regs[ts->type] & mask;
            }
            *pset = set;

            /* Mark all live temporaries as 'maybe clobbered'. This should
             * come BEFORE `la_record_life` for call clobbering ops, so as
             * to catch all temporaries that might be clobbered.  */
            ts->state |= TS_MAY_CLOBBER;
        }
    }
}

static void la_record_life(TCGOp *op, uint8_t i, bool is_oargs)
{
    const TCGTemp *ts = arg_temp(op->args[i]);

    /* The argument is dead after this op, free the register it uses.
     * For input argument, it might be the very output of the current
     * op that kills the input, free the register early to benefit the
     * register allocation of the output.  */
    if (ts->state & TS_DEAD) {
        op->life |= DEAD_ARG << i;
    }
    /* The argument is still alive after this op, but another op before
     * the VERY NEXT USE of this argument might clobber the register it
     * uses, check if the argument indeed uses a caller-saved register,
     * and free it early if needed.
     * Note that `call` and `tlb_check` will clobber different sets of
     * registers, only the intersection of those registers will be early
     * freed.  */
    if (ts->state & TS_MAY_CLOBBER) {
        tcg_debug_assert(!(ts->state & TS_DEAD));
        op->life |= CLOBBER_ARG << i;
    }
    /* The output argument should be synced back to its canonical memory
     * location at the end of this op.  */
    if (is_oargs && (ts->state & TS_SYNC)) {
        op->life |= SYNC_ARG << i;
    }
    op->next_use[i] = la_next_use(ts);
}

/* Liveness analysis: update op->life to record if any argument
 * is dead, needs to be synced, or may be clobbered by the time
 * the op ends. Instructions updating dead temporaries will be
 * removed.  */
static void liveness_pass_1(TCGContext *s)
{
    size_t nb_globals = s->nb_globals;
    size_t nb_temps = s->nb_temps;
    TCGOp *op, *op_prev;
    TempLivenessInfo *infos;
    size_t i;

    infos = tcg_malloc(sizeof(TempLivenessInfo) * nb_temps);
    for (i = 0; i < nb_temps; ++i) {
        s->temps[i].state_ptr = &infos[i];
    }
    s->current_insn = 0;

    /* ??? Should be redundant with the exit_tb that ends the TB.  */
    la_func_end(s, nb_globals, nb_temps);

    QTAILQ_FOREACH_REVERSE_SAFE(op, &s->ops, link, op_prev) {
        uint8_t nb_iargs, nb_oargs;
        TCGOpcode opc_new, opc_new2;
        bool have_opc_new2;
        TCGTemp *ts;
        TCGOpcode opc = op->opc;
        const TCGOpDef *def = &tcg_op_defs[opc];

        tcg_debug_assert(op->life == 0);
        switch (opc) {
        case INDEX_op_call:
            {
                uint16_t call_flags;
                uint8_t nb_call_regs;

                nb_oargs = TCGOP_CALLO(op);
                nb_iargs = TCGOP_CALLI(op);
                call_flags = op->args[nb_oargs + nb_iargs + 1];

                /* Pure functions can be removed if their result is unused.  */
                if (call_flags & TCG_CALL_NO_SIDE_EFFECTS) {
                    for (i = 0; i < nb_oargs; i++) {
                        ts = arg_temp(op->args[i]);
                        if (ts->state != TS_DEAD) {
                            goto do_not_remove_call;
                        }
                    }
                    goto do_remove;
                }
            do_not_remove_call:
                /* Output arguments are dead.  */
                for (i = 0; i < nb_oargs; i++) {
                    ts = arg_temp(op->args[i]);

                    /* Not used -- it will be tcg_target_call_oarg_regs[i].  */
                    op->output_pref[i] = 0;

                    la_record_life(op, i, true);
                    ts->state = TS_DEAD;
                    la_reset_pref(ts);
                }

                if (!(call_flags & (TCG_CALL_NO_WRITE_GLOBALS |
                                    TCG_CALL_NO_READ_GLOBALS))) {
                    la_global_kill(s, nb_globals);
                } else if (!(call_flags & TCG_CALL_NO_READ_GLOBALS)) {
                    la_global_sync(s, nb_globals);
                }

                /* For all live registers, remove call-clobbered prefs.  */
                la_cross_call(s, nb_temps, false);

                /* Record arguments that die or may clobbered in this call.  */
                for (i = nb_oargs; i < nb_iargs + nb_oargs; i++) {
                    if (!(ts = arg_temp(op->args[i]))) {
                        continue;
                    }
                    la_record_life(op, i, false);
                    ts->state &= ~TS_MAY_CLOBBER;
                    la_set_next_use(ts, s->current_insn);
                }

                nb_call_regs = ARRAY_SIZE(tcg_target_call_iarg_regs);

                /* Input arguments are live for preceding opcodes.  */
                for (i = 0; i < nb_iargs; i++) {
                    ts = arg_temp(op->args[i + nb_oargs]);
                    if (ts && ts->state & TS_DEAD) {
                        /* For those arguments that die, and will be allocated
                         * in registers, clear the register set for that arg,
                         * to be filled in below.  For args that will be on
                         * the stack, reset to any available reg.
                         */
                        *la_temp_pref(ts)
                            = (i < nb_call_regs ? 0 :
                               tcg_target_available_regs[ts->type]);
                        ts->state &= ~TS_DEAD;
                    }
                }

                /* For each input argument, add its input register to prefs.
                   If a temp is used once, this produces a single set bit.  */
                for (i = 0; i < MIN(nb_call_regs, nb_iargs); i++) {
                    ts = arg_temp(op->args[i + nb_oargs]);
                    if (ts) {
                        tcg_regset_set_reg(*la_temp_pref(ts),
                                           tcg_target_call_iarg_regs[i]);
                    }
                }
            }
            break;
        case INDEX_op_insn_start:
            break;
        case INDEX_op_discard:
            /* Mark the temporary as dead.  */
            ts = arg_temp(op->args[0]);
            ts->state = TS_DEAD;
            la_reset_pref(ts);
            la_record_life(op, 0, true);
            break;
        case INDEX_op_side_effect:
            /* Sync all TEMP_GLOBALs back to their canonical locations within
             * CPUArchState, JUST in case of the execution bailout due to the
             * ridiculous possibility of triggering memory exceptions.  */
            la_global_sync(s, nb_globals);
            break;
        case INDEX_op_tlb_check:
        case INDEX_op_itlb_check:
            nb_oargs = 0;
            nb_iargs = 3;
            la_cross_call(s, nb_temps, true);
            goto do_not_remove2;

        case INDEX_op_add2_i32:
            opc_new = INDEX_op_add_i32;
            goto do_addsub2;
        case INDEX_op_sub2_i32:
            opc_new = INDEX_op_sub_i32;
            goto do_addsub2;
        case INDEX_op_add2_i64:
            opc_new = INDEX_op_add_i64;
            goto do_addsub2;
        case INDEX_op_sub2_i64:
            opc_new = INDEX_op_sub_i64;
        do_addsub2:
            nb_iargs = 4;
            nb_oargs = 2;
            /* Test if the high part of the operation is dead, but not
               the low part.  The result can be optimized to a simple
               add or sub.  This happens often for x86_64 guest when the
               cpu mode is set to 32 bit.  */
            if (arg_temp(op->args[1])->state == TS_DEAD) {
                if (arg_temp(op->args[0])->state == TS_DEAD) {
                    goto do_remove;
                }
                /* Replace the opcode and adjust the args in place,
                   leaving 3 unused args at the end.  */
                op->opc = opc = opc_new;
                op->args[1] = op->args[2];
                op->args[2] = op->args[4];
                /* Fall through and mark the single-word operation live.  */
                nb_iargs = 2;
                nb_oargs = 1;
            }
            goto do_not_remove;

        case INDEX_op_mulu2_i32:
            opc_new = INDEX_op_mul_i32;
            opc_new2 = INDEX_op_muluh_i32;
            have_opc_new2 = TCG_TARGET_HAS_muluh_i32;
            goto do_mul2;
        case INDEX_op_muls2_i32:
            opc_new = INDEX_op_mul_i32;
            opc_new2 = INDEX_op_mulsh_i32;
            have_opc_new2 = TCG_TARGET_HAS_mulsh_i32;
            goto do_mul2;
        case INDEX_op_mulu2_i64:
            opc_new = INDEX_op_mul_i64;
            opc_new2 = INDEX_op_muluh_i64;
            have_opc_new2 = TCG_TARGET_HAS_muluh_i64;
            goto do_mul2;
        case INDEX_op_muls2_i64:
            opc_new = INDEX_op_mul_i64;
            opc_new2 = INDEX_op_mulsh_i64;
            have_opc_new2 = TCG_TARGET_HAS_mulsh_i64;
            goto do_mul2;
        do_mul2:
            nb_iargs = 2;
            nb_oargs = 2;
            if (arg_temp(op->args[1])->state == TS_DEAD) {
                if (arg_temp(op->args[0])->state == TS_DEAD) {
                    /* Both parts of the operation are dead.  */
                    goto do_remove;
                }
                /* The high part of the operation is dead; generate the low. */
                op->opc = opc = opc_new;
                op->args[1] = op->args[2];
                op->args[2] = op->args[3];
            } else if (arg_temp(op->args[0])->state == TS_DEAD && have_opc_new2) {
                /* The low part of the operation is dead; generate the high. */
                op->opc = opc = opc_new2;
                op->args[0] = op->args[1];
                op->args[1] = op->args[2];
                op->args[2] = op->args[3];
            } else {
                goto do_not_remove;
            }
            /* Mark the single-word operation live.  */
            nb_oargs = 1;
            goto do_not_remove;

        default:
            /* XXX: optimize by hardcoding common cases (e.g. triadic ops) */
            nb_iargs = def->nb_iargs;
            nb_oargs = def->nb_oargs;

            /* Test if the operation can be removed because all
               its outputs are dead. We assume that nb_oargs == 0
               implies side effects */
            if (!(def->flags & TCG_OPF_SIDE_EFFECTS) && nb_oargs != 0) {
                for (i = 0; i < nb_oargs; i++) {
                    if (arg_temp(op->args[i])->state != TS_DEAD) {
                        goto do_not_remove;
                    }
                }
                goto do_remove;
            }
            goto do_not_remove;

        do_remove:
            tcg_op_remove(s, op);
            continue;

        do_not_remove:
            /* Output arguments are dead.  */
            for (i = 0; i < nb_oargs; i++) {
                ts = arg_temp(op->args[i]);

                /* Remember the preference of the uses that followed.  */
                op->output_pref[i] = *la_temp_pref(ts);

                la_record_life(op, i, true);
                ts->state = TS_DEAD;
                la_reset_pref(ts);
            }

            /* If end of basic block, update.  */
            if (def->flags & TCG_OPF_BB_EXIT) {
                la_func_end(s, nb_globals, nb_temps);
            } else if (def->flags & TCG_OPF_COND_BRANCH) {
                la_bb_sync(s, nb_globals, nb_temps);
            } else if (def->flags & TCG_OPF_BB_END) {
                la_bb_end(s, nb_globals, nb_temps);
            } else if (def->flags & TCG_OPF_SIDE_EFFECTS) {
                la_global_sync(s, nb_globals);
            }
            if (def->flags & TCG_OPF_CALL_CLOBBER) {
                la_cross_call(s, nb_temps, false);
            }

        do_not_remove2:
            /* Record arguments that die or may clobbered in this opcode.  */
            for (i = nb_oargs; i < nb_oargs + nb_iargs; i++) {
                ts = arg_temp(op->args[i]);
                la_record_life(op, i, false);
                ts->state &= ~TS_MAY_CLOBBER;
                la_set_next_use(ts, s->current_insn);
            }

            /* Input arguments are live for preceding opcodes.  */
            for (i = nb_oargs; i < nb_oargs + nb_iargs; i++) {
                ts = arg_temp(op->args[i]);
                if (ts->state & TS_DEAD) {
                    /* For operands that were dead, initially allow
                       all regs for the type.  */
                    *la_temp_pref(ts) = tcg_target_available_regs[ts->type];
                    ts->state &= ~TS_DEAD;
                }
            }

            /* Incorporate constraints for this operand.  */
            switch (opc) {
            case INDEX_op_mov_i32:
            case INDEX_op_mov_i64:
                /* Note that these are TCG_OPF_NOT_PRESENT and do not
                   have proper constraints.  That said, special case
                   moves to propagate preferences backward.  */
                if (IS_DEAD_ARG(1)) {
                    *la_temp_pref(arg_temp(op->args[0]))
                        = *la_temp_pref(arg_temp(op->args[1]));
                }
                break;

            default:
                for (i = nb_oargs; i < nb_oargs + nb_iargs; i++) {
                    const TCGArgConstraint *ct = &def->args_ct[i];
                    TCGRegSet set, *pset;

                    ts = arg_temp(op->args[i]);
                    pset = la_temp_pref(ts);
                    set = *pset;

                    set &= ct->regs;
                    if (ct->ialias) {
                        set &= op->output_pref[ct->alias_index];
                    }
                    /* If the combination is not possible, restart.  */
                    if (set == 0) {
                        set = ct->regs;
                    }
                    *pset = set;
                }
                break;
            }
            break;
        }
        s->current_insn++;
    }
}

/* Liveness analysis: Convert indirect regs to direct temporaries.  */
static bool liveness_pass_2(TCGContext *s)
{
    size_t nb_globals = s->nb_globals;
    size_t nb_temps, i;
    bool changes = false;
    TCGOp *op, *op_next;

    /* Create a temporary for each indirect global.  */
    for (i = 0; i < nb_globals; ++i) {
        TCGTemp *its = &s->temps[i];
        if (its->indirect_reg) {
            TCGTemp *dts = tcg_temp_alloc(s, its->type, TEMP_NORMAL);
            its->state_ptr = dts;
        } else {
            its->state_ptr = NULL;
        }
        /* All globals begin dead.  */
        its->state = TS_DEAD;
    }
    for (nb_temps = s->nb_temps; i < nb_temps; ++i) {
        TCGTemp *its = &s->temps[i];
        its->state_ptr = NULL;
        its->state = TS_DEAD;
    }

    QTAILQ_FOREACH_SAFE(op, &s->ops, link, op_next) {
        TCGOpcode opc = op->opc;
        const TCGOpDef *def = &tcg_op_defs[opc];
        uint8_t nb_iargs, nb_oargs;
        uint16_t call_flags;
        TCGTemp *arg_ts, *dir_ts;

        if (opc == INDEX_op_call) {
            nb_oargs = TCGOP_CALLO(op);
            nb_iargs = TCGOP_CALLI(op);
            call_flags = op->args[nb_oargs + nb_iargs + 1];
        } else {
            nb_iargs = def->nb_iargs;
            nb_oargs = def->nb_oargs;

            /* Set flags similar to how calls require.  */
            if (def->flags & TCG_OPF_COND_BRANCH) {
                /* Like reading globals: sync_globals */
                call_flags = TCG_CALL_NO_WRITE_GLOBALS;
            } else if (def->flags & TCG_OPF_BB_END) {
                /* Like writing globals: save_globals */
                call_flags = 0;
            } else if (def->flags & TCG_OPF_SIDE_EFFECTS) {
                /* Like reading globals: sync_globals */
                call_flags = TCG_CALL_NO_WRITE_GLOBALS;
            } else {
                /* No effect on globals.  */
                call_flags = (TCG_CALL_NO_READ_GLOBALS |
                              TCG_CALL_NO_WRITE_GLOBALS);
            }
        }

        /* Make sure that input arguments are available.  */
        for (i = nb_oargs; i < nb_iargs + nb_oargs; i++) {
            arg_ts = arg_temp(op->args[i]);
            if (arg_ts) {
                dir_ts = arg_ts->state_ptr;
                if (dir_ts && arg_ts->state == TS_DEAD) {
                    TCGOpcode lopc = (arg_ts->type == TCG_TYPE_I32
                                      ? INDEX_op_ld_i32
                                      : INDEX_op_ld_i64);
                    TCGOp *lop = tcg_op_insert_before(s, op, lopc);

                    lop->args[0] = temp_arg(dir_ts);
                    lop->args[1] = temp_arg(arg_ts->mem_base);
                    lop->args[2] = arg_ts->mem_offset;

                    /* Loaded, but synced with memory.  */
                    arg_ts->state = TS_SYNC;
                }
            }
        }

        /* Perform input replacement, and mark inputs that became dead.
           No action is required except keeping temp_state up to date
           so that we reload when needed.  */
        for (i = nb_oargs; i < nb_iargs + nb_oargs; i++) {
            arg_ts = arg_temp(op->args[i]);
            if (arg_ts) {
                dir_ts = arg_ts->state_ptr;
                if (dir_ts) {
                    op->args[i] = temp_arg(dir_ts);
                    changes = true;
                    if (IS_DEAD_ARG(i)) {
                        arg_ts->state = TS_DEAD;
                    }
                }
            }
        }

        /* Liveness analysis should ensure that the following are
           all correct, for call sites and basic block end points.  */
        if (call_flags & TCG_CALL_NO_READ_GLOBALS) {
            /* Nothing to do */
        } else if (call_flags & TCG_CALL_NO_WRITE_GLOBALS) {
            for (i = 0; i < nb_globals; ++i) {
                /* Liveness should see that globals are synced back,
                   that is, either TS_DEAD or TS_SYNC.  */
                arg_ts = &s->temps[i];
                tcg_debug_assert(arg_ts->state_ptr == 0
                                 || arg_ts->state != 0);
            }
        } else {
            for (i = 0; i < nb_globals; ++i) {
                /* Liveness should see that globals are saved back,
                   that is, TS_DEAD, waiting to be reloaded.  */
                arg_ts = &s->temps[i];
                tcg_debug_assert(arg_ts->state_ptr == 0
                                 || arg_ts->state == TS_DEAD);
            }
        }

        /* Outputs become available.  */
        if (opc == INDEX_op_mov_i32 || opc == INDEX_op_mov_i64) {
            arg_ts = arg_temp(op->args[0]);
            dir_ts = arg_ts->state_ptr;
            if (dir_ts) {
                op->args[0] = temp_arg(dir_ts);
                changes = true;

                /* The output is now live and modified.  */
                arg_ts->state = 0;

                if (NEED_SYNC_ARG(0)) {
                    TCGOpcode sopc = (arg_ts->type == TCG_TYPE_I32
                                      ? INDEX_op_st_i32
                                      : INDEX_op_st_i64);
                    TCGOp *sop = tcg_op_insert_after(s, op, sopc);
                    TCGTemp *out_ts = dir_ts;

                    if (IS_DEAD_ARG(0)) {
                        out_ts = arg_temp(op->args[1]);
                        arg_ts->state = TS_DEAD;
                        tcg_op_remove(s, op);
                    } else {
                        arg_ts->state = TS_SYNC;
                    }

                    sop->args[0] = temp_arg(out_ts);
                    sop->args[1] = temp_arg(arg_ts->mem_base);
                    sop->args[2] = arg_ts->mem_offset;
                } else {
                    tcg_debug_assert(!IS_DEAD_ARG(0));
                }
            }
        } else {
            for (i = 0; i < nb_oargs; i++) {
                arg_ts = arg_temp(op->args[i]);
                dir_ts = arg_ts->state_ptr;
                if (!dir_ts) {
                    continue;
                }
                op->args[i] = temp_arg(dir_ts);
                changes = true;

                /* The output is now live and modified.  */
                arg_ts->state = 0;

                /* Sync outputs upon their last write.  */
                if (NEED_SYNC_ARG(i)) {
                    TCGOpcode sopc = (arg_ts->type == TCG_TYPE_I32
                                      ? INDEX_op_st_i32
                                      : INDEX_op_st_i64);
                    TCGOp *sop = tcg_op_insert_after(s, op, sopc);

                    sop->args[0] = temp_arg(dir_ts);
                    sop->args[1] = temp_arg(arg_ts->mem_base);
                    sop->args[2] = arg_ts->mem_offset;

                    arg_ts->state = TS_SYNC;
                }
                /* Drop outputs that are dead.  */
                if (IS_DEAD_ARG(i)) {
                    arg_ts->state = TS_DEAD;
                }
            }
        }
    }

    return changes;
}

/*
 * TCG register allocation facilities
 */

typedef enum TCGTempVal {
    TEMP_VAL_DEAD,
    TEMP_VAL_REG,
    TEMP_VAL_MEM,
    TEMP_VAL_CONST,
    TEMP_VAL_INVALID,
} TCGTempVal;

static inline TCGTempVal ts_val_type(TCGTemp *ts)
{
    tcg_debug_assert(ts->state < TEMP_VAL_INVALID);
    return ts->state;
}

static inline void ts_set_val_type(TCGTemp *ts, TCGTempVal val_type)
{
    ts->state = val_type;
}

static inline uint16_t ts_next_use(TCGTemp *ts)
{
    return (uintptr_t) ts->state_ptr;
}

static inline void ts_set_next_use(TCGTemp *ts, uintptr_t next_use)
{
    ts->state_ptr = (void *) next_use;
}

static void tcg_reg_alloc_start(TCGContext *s)
{
    for (size_t i = 0; i < s->nb_temps; i++) {
        TCGTemp *ts = &s->temps[i];
        TCGTempVal val_type = TEMP_VAL_MEM;

        switch (ts->kind) {
        case TEMP_CONST:
            val_type = TEMP_VAL_CONST;
            break;
        case TEMP_FIXED:
            val_type = TEMP_VAL_REG;
            break;
        case TEMP_GLOBAL:
            break;
        case TEMP_NORMAL:
            val_type = TEMP_VAL_DEAD;
            /* fall through */
        case TEMP_LOCAL:
            ts->mem_allocated = false;
            break;
        default:
            g_assert_not_reached();
        }
        ts_set_val_type(ts, val_type);
    }

    memset(s->reg_to_temp, 0, sizeof(s->reg_to_temp));
}

#ifdef CONFIG_DEBUG_TCG
static void dump_regs(TCGContext *s)
{
    TCGTemp *ts;
    size_t i;
    char buf[64];

    for(i = 0; i < s->nb_temps; i++) {
        ts = &s->temps[i];
        printf("  %10s: ", tcg_get_arg_str_ptr(s, buf, sizeof(buf), ts));
        switch(ts_val_type(ts)) {
        case TEMP_VAL_REG:
            printf("%s", tcg_target_reg_names[ts->reg]);
            break;
        case TEMP_VAL_MEM:
            printf("%d(%s)", (int)ts->mem_offset,
                   tcg_target_reg_names[ts->mem_base->reg]);
            break;
        case TEMP_VAL_CONST:
            printf("$0x%" PRIx64, ts->val);
            break;
        case TEMP_VAL_DEAD:
            printf("D");
            break;
        default:
            printf("???");
            break;
        }
        printf("\n");
    }

    for(i = 0; i < TCG_TARGET_NB_REGS; i++) {
        if (s->reg_to_temp[i] != NULL) {
            printf("%s: %s\n",
                   tcg_target_reg_names[i],
                   tcg_get_arg_str_ptr(s, buf, sizeof(buf), s->reg_to_temp[i]));
        }
    }
}

static void check_regs(TCGContext *s)
{
    size_t reg, k;
    TCGTemp *ts;
    char buf[64];

    for (reg = 0; reg < TCG_TARGET_NB_REGS; reg++) {
        ts = s->reg_to_temp[reg];
        if (ts != NULL) {
            if (ts_val_type(ts) != TEMP_VAL_REG || ts->reg != reg) {
                printf("Inconsistency for register %s:\n",
                       tcg_target_reg_names[reg]);
                goto fail;
            }
        }
    }
    for (k = 0; k < s->nb_temps; k++) {
        ts = &s->temps[k];
        if (ts_val_type(ts) == TEMP_VAL_REG
            && ts->kind != TEMP_FIXED
            && s->reg_to_temp[ts->reg] != ts) {
            printf("Inconsistency for temp %s:\n",
                   tcg_get_arg_str_ptr(s, buf, sizeof(buf), ts));
        fail:
            printf("reg state:\n");
            dump_regs(s);
            tcg_abort();
        }
    }
}
#endif

static void temp_allocate_frame(TCGContext *s, TCGTemp *ts)
{
    intptr_t off, size, align;

    switch (ts->type) {
    case TCG_TYPE_I32:
        size = align = 4;
        break;
    case TCG_TYPE_I64:
    case TCG_TYPE_V64:
        size = align = 8;
        break;
    case TCG_TYPE_V128:
        size = align = 16;
        break;
    case TCG_TYPE_V256:
        /* Note that we do not require aligned storage for V256. */
        size = 32, align = 16;
        break;
    default:
        g_assert_not_reached();
    }

    assert(align <= TCG_TARGET_STACK_ALIGN);
    off = ROUND_UP(s->current_frame_offset, align);

    if (off + size > s->frame_end) {
        tcg_signal_tb_overflow__siglongjmp(s);
    }
    s->current_frame_offset = off + size;

    ts->mem_offset = off;
#if defined(__sparc__)
    ts->mem_offset += TCG_TARGET_STACK_BIAS;
#endif
    ts->mem_base = s->frame_temp;
    ts->mem_allocated = true;
}

static bool temp_storei(TCGContext *s, TCGTemp *ts, TCGType type, TCGArg val)
{
    if (!ts->mem_allocated) {
        temp_allocate_frame(s, ts);
    }
    return tcg_out_sti(s, type, val, ts->mem_base->reg, ts->mem_offset);
}

static void temp_store(TCGContext *s, TCGTemp *ts, TCGType type, TCGReg reg)
{
    if (!ts->mem_allocated) {
        temp_allocate_frame(s, ts);
    }
    tcg_out_st(s, type, reg, ts->mem_base->reg, ts->mem_offset);
}

/* Mark a temporary as free or dead.  If 'free_or_dead' is negative,
 * mark it free; otherwise mark it dead.  */
static void temp_free_or_dead(TCGContext *s, TCGTemp *ts, int free_or_dead)
{
    TCGTempVal val_type;

    tcg_debug_assert((free_or_dead < 0) ||
                     (ts_next_use(ts) == s->current_insn));

    switch (ts->kind) {
    case TEMP_FIXED:
        return;
    case TEMP_GLOBAL:
    case TEMP_LOCAL:
        val_type = TEMP_VAL_MEM;
        break;
    case TEMP_NORMAL:
        val_type = free_or_dead < 0 ? TEMP_VAL_MEM : TEMP_VAL_DEAD;
        break;
    case TEMP_CONST:
        val_type = TEMP_VAL_CONST;
        break;
    default:
        g_assert_not_reached();
    }
    if (ts_val_type(ts) == TEMP_VAL_REG) {
        s->reg_to_temp[ts->reg] = NULL;
    }
    ts_set_val_type(ts, val_type);
}

/* Mark a temporary as dead.  */
static inline void temp_dead(TCGContext *s, TCGTemp *ts)
{
    temp_free_or_dead(s, ts, 1);
}

static void temp_load(TCGContext *, TCGTemp *, TCGRegSet, TCGRegSet);

/* Sync a temporary to memory. 'allocated_regs' is used in case a temporary
 * registers needs to be allocated to store a constant.  If 'free_or_dead'
 * is non-zero, subsequently release the temporary; if it is positive, the
 * temp is dead; if it is negative, the temp is free.  */
static inline void temp_sync_internal(TCGContext *s, TCGTemp *ts,
                                      int free_or_dead,
                                      TCGRegSet allocated_regs,
                                      TCGRegSet preferred_regs)
{
    if (!temp_readonly(ts) && !ts->mem_coherent) {
        switch (ts_val_type(ts)) {
        case TEMP_VAL_CONST:
            if (temp_storei(s, ts, ts->type, ts->val)) {
                break;
            }
            temp_load(s, ts, tcg_target_available_regs[ts->type] &
                      ~allocated_regs, preferred_regs);
            /* fallthrough */
        case TEMP_VAL_REG:
            temp_store(s, ts, ts->type, ts->reg);
            break;
        case TEMP_VAL_MEM:
            break;
        case TEMP_VAL_DEAD:
        default:
            tcg_abort();
        }
        ts->mem_coherent = true;
    }
    if (free_or_dead) {
        temp_free_or_dead(s, ts, free_or_dead);
    }
}

static void temp_sync(TCGContext *s, TCGTemp *ts, int free_or_dead)
{
    /* Only when syncing TEMP_VAL_CONST temporaries do we need
     * `allocated_regs` and `preferred_regs`.  */
    tcg_debug_assert(ts_val_type(ts) != TEMP_VAL_CONST);
    temp_sync_internal(s, ts, free_or_dead, 0, 0);
}

/* Free register 'reg' by spilling the corresponding temporary if necessary.  */
static void tcg_reg_free(TCGContext *s, TCGReg reg)
{
    TCGTemp *ts = s->reg_to_temp[reg];
    if (ts != NULL) {
        temp_sync(s, ts, -1);
    }
}

static bool temp_with_reg_in_clobber_list(TCGTemp *ts)
{
    if (ts_val_type(ts) != TEMP_VAL_REG) {
        return false;
    } else if (!tcg_regset_test_reg(tcg_target_tlb_check_clobber_regs,
                                    ts->reg)) {
        return false;
    }
    return true;
}

#define DO_CLOBBER_ARG(n, ts)   \
    (!!MAY_CLOBBER_ARG(n) && temp_with_reg_in_clobber_list(ts))

static void temp_clobber(TCGContext *s, TCGTemp *ts)
{
    tcg_debug_assert(temp_with_reg_in_clobber_list(ts));
    tcg_debug_assert(s->reg_to_temp[ts->reg] == ts);
    tcg_reg_free(s, ts->reg);
}

/**
 * tcg_reg_alloc:
 * @required_regs: Set of registers in which we must allocate.
 * @preferred_regs: Set of registers we should prefer.
 * @rev: True if we search the registers in "indirect" order.
 *
 * The allocated register must be in @required_regs, but if we
 * can put it in @preferred_regs we may save a move later.
 */
static TCGReg tcg_reg_alloc(TCGContext *s, TCGRegSet required_regs,
                            TCGRegSet preferred_regs, bool rev)
{
    size_t i, j, f;
    const TCGReg *order = rev ? indirect_reg_alloc_order
                              : tcg_target_reg_alloc_order;
    TCGRegSet reg_ct[2];
    TCGReg reg;

    tcg_debug_assert((reg_ct[1] = required_regs) != 0);
    reg_ct[0] = reg_ct[1] & preferred_regs;

    /* Skip the preferred_regs option if it cannot be satisfied,
     * or if the preference made no difference.  */
    f = reg_ct[0] == 0 || reg_ct[0] == reg_ct[1];

    /* Try free registers, preferences first.  */
    for (j = f; j < 2; j++) {
        if (tcg_regset_single(reg_ct[j])) {
            /* One register in the set.  */
            reg = tcg_regset_first(reg_ct[j]);
            if (s->reg_to_temp[reg] == NULL) {
                return reg;
            }
        } else {
            for (i = 0; i < ARRAY_SIZE(tcg_target_reg_alloc_order); i++) {
                reg = order[i];
                if (s->reg_to_temp[reg] == NULL &&
                    tcg_regset_test_reg(reg_ct[j], reg)) {
                    return reg;
                }
            }
        }
    }

    /* We must spill something.  */
    if (tcg_regset_single(reg_ct[f])) {
        /* One register in the set.  */
        reg = tcg_regset_first(reg_ct[f]);
    } else {
        TCGTemp *ts = NULL, *ts2;

        for (i = 0; i < ARRAY_SIZE(tcg_target_reg_alloc_order); i++) {
            reg = order[i];
            if (tcg_regset_test_reg(reg_ct[f], reg)) {
                tcg_debug_assert((ts2 = s->reg_to_temp[reg]) != NULL);
                /* Choose the temporary with later (i.e. numerically
                 * smaller) .next_use to spill.  */
                if (!ts || ts_next_use(ts2) < ts_next_use(ts)) {
                    ts = ts2;
                }
            }
        }
        tcg_debug_assert(ts_val_type(ts) == TEMP_VAL_REG);
        reg = ts->reg;
    }
    tcg_reg_free(s, reg);
    return reg;
}

/* Commit register allocation to a temporary.  */
static void temp_commit_register(TCGContext *s, TCGTemp *ts, TCGReg reg,
                                 bool clear_coherent)
{
    if (clear_coherent) {
        /* Temp value is modified, so the value kept in memory is
         * potentially not the same.  */
        ts->mem_coherent = false;
    }
    ts->reg = reg;
    ts_set_val_type(ts, TEMP_VAL_REG);
    s->reg_to_temp[reg] = ts;
}

/* Make sure the temporary is in a register.  */
static void temp_load(TCGContext *s, TCGTemp *ts, TCGRegSet required_regs,
                      TCGRegSet preferred_regs)
{
    TCGReg reg;

    switch (ts_val_type(ts)) {
    case TEMP_VAL_REG:
        return;
    case TEMP_VAL_CONST:
        reg = tcg_reg_alloc(s, required_regs, preferred_regs, ts->indirect_base);
        if (ts->type <= TCG_TYPE_I64) {
            tcg_out_movi(s, ts->type, reg, ts->val);
        } else {
            uint64_t val = ts->val;
            MemOp vece = MO_64;

            /*
             * Find the minimal vector element that matches the constant.
             * The targets will, in general, have to do this search anyway,
             * do this generically.
             */
            if (val == dup_const(MO_8, val)) {
                vece = MO_8;
            } else if (val == dup_const(MO_16, val)) {
                vece = MO_16;
            } else if (val == dup_const(MO_32, val)) {
                vece = MO_32;
            }

            tcg_out_dupi_vec(s, ts->type, vece, reg, ts->val);
        }
        break;
    case TEMP_VAL_MEM:
        reg = tcg_reg_alloc(s, required_regs, preferred_regs, ts->indirect_base);
        tcg_out_ld(s, ts->type, reg, ts->mem_base->reg, ts->mem_offset);
        ts->mem_coherent = true;
        break;
    case TEMP_VAL_DEAD:
    default:
        tcg_abort();
    }
    temp_commit_register(s, ts, reg, false);
}

/* The liveness analysis already ensures that globals are back in memory.
 * Keep an tcg_debug_assert for safety.  */
static void temp_save(TCGTemp *ts)
{
    tcg_debug_assert(ts_val_type(ts) == TEMP_VAL_MEM || temp_readonly(ts));
}

/* Save globals to their canonical location and assume they can be
 * modified by the following code.  */
static void save_globals(TCGContext *s)
{
    for (size_t i = 0; i < s->nb_globals; i++) {
        temp_save(&s->temps[i]);
    }
}

/* At the end of a basic block, we assume all temporaries are dead and
 * all globals are stored at their canonical location.  */
static void tcg_reg_alloc_bb_end(TCGContext *s)
{
    save_globals(s);

    for (size_t i = s->nb_globals; i < s->nb_temps; i++) {
        TCGTemp *ts = &s->temps[i];

        switch (ts->kind) {
        case TEMP_LOCAL:
            temp_save(ts);
            break;
        case TEMP_NORMAL:
            /* The liveness analysis already ensures that temps are dead.
               Keep an tcg_debug_assert for safety. */
            tcg_debug_assert(ts_val_type(ts) == TEMP_VAL_DEAD);
            break;
        case TEMP_CONST:
            /* Similarly, we should have freed any allocated register. */
            tcg_debug_assert(ts_val_type(ts) == TEMP_VAL_CONST);
            break;
        default:
            g_assert_not_reached();
        }
    }
}

/* Sync globals to their canonical location and assume they can be
 * read by the following code.  */
static void sync_globals(TCGContext *s)
{
    for (size_t i = 0; i < s->nb_globals; i++) {
        TCGTemp *ts = &s->temps[i];
        tcg_debug_assert(ts_val_type(ts) != TEMP_VAL_REG
                         || ts->kind == TEMP_FIXED
                         || ts->mem_coherent);
    }
}

/*
 * At a conditional branch, we assume all temporaries are dead and
 * all globals and local temps are synced to their location.
 */
static void tcg_reg_alloc_cbranch(TCGContext *s)
{
    sync_globals(s);

    for (size_t i = s->nb_globals; i < s->nb_temps; i++) {
        TCGTemp *ts = &s->temps[i];
        /*
         * The liveness analysis already ensures that temps are dead.
         * Keep tcg_debug_asserts for safety.
         */
        switch (ts->kind) {
        case TEMP_LOCAL:
            tcg_debug_assert(ts_val_type(ts) != TEMP_VAL_REG ||
                             ts->mem_coherent);
            break;
        case TEMP_NORMAL:
            tcg_debug_assert(ts_val_type(ts) == TEMP_VAL_DEAD);
            break;
        case TEMP_CONST:
            break;
        default:
            g_assert_not_reached();
        }
    }
}

/* Check an output temporary is in proper state, i.e., with its
 * val_type set by previous temp_dead() or tcg_reg_alloc_start().  */
static inline void tcg_reg_alloc_check_output(TCGTemp *ots)
{
    /* Read-only temporaries should not be modified.  */
    tcg_debug_assert(!temp_readonly(ots));

    switch (ots->kind) {
    case TEMP_NORMAL:
        tcg_debug_assert(ts_val_type(ots) == TEMP_VAL_DEAD);
        break;
    case TEMP_LOCAL:
    case TEMP_GLOBAL:
        tcg_debug_assert(ts_val_type(ots) == TEMP_VAL_MEM);
        break;
    default:
        g_assert_not_reached();
    }
}

/*
 * Specialized code generation for INDEX_op_mov_* with a constant.
 */
static void tcg_reg_alloc_do_movi(TCGContext *s, TCGTemp *ots, TCGTemp *ts,
                                  const TCGOp *op, TCGRegSet preferred_regs)
{
    /* The MOVI is not explicitly generated here.  */
    ots->val = ts->val;
    ots->mem_coherent = false;
    ts_set_val_type(ots, TEMP_VAL_CONST);

    /* No need to clobber, as neither of {ts, ots} is of TEMP_VAL_CONST.  */
    ts_set_next_use(ts, op->next_use[1]);
    if (IS_DEAD_ARG(1)) {
        temp_dead(s, ts);
    }
    ts_set_next_use(ots, op->next_use[0]);
    if (NEED_SYNC_ARG(0)) {
        temp_sync_internal(s, ots, IS_DEAD_ARG(0), s->reserved_regs,
                           preferred_regs);
        /* Register may need to be allocated to SYNC the constant, which
         * might happen to be also in the clobber list.  */
        if (unlikely(DO_CLOBBER_ARG(0, ots))) {
            temp_clobber(s, ots);
        }
    } else {
        /* Mov to a non-saved dead register makes no sense.  */
        tcg_debug_assert(!IS_DEAD_ARG(0));
    }
}

/*
 * Specialized code generation for INDEX_op_mov_*.
 */
static void tcg_reg_alloc_mov(TCGContext *s, const TCGOp *op)
{
    TCGRegSet allocated_regs, preferred_regs;
    TCGTemp *ts, *ots;
    TCGType otype, itype;
    TCGReg reg;

    allocated_regs = s->reserved_regs;
    preferred_regs = op->output_pref[0];
    ots = arg_temp(op->args[0]);
    ts = arg_temp(op->args[1]);

    /* Output temporary should be well-formed.  */
    tcg_reg_alloc_check_output(ots);

    /* Note that otype != itype for no-op truncation.  */
    otype = ots->type;
    itype = ts->type;

    if (ts_val_type(ts) == TEMP_VAL_CONST) {
        /* Propagate constant or generate sti.  */
        tcg_reg_alloc_do_movi(s, ots, ts, op, preferred_regs);
        return;
    }

    /* If the source value is in memory we're going to be forced
       to have it in a register in order to perform the copy.  Copy
       the SOURCE value into its own register first, that way we
       don't have to reload SOURCE the next time it is used. */
    if (ts_val_type(ts) == TEMP_VAL_MEM) {
        temp_load(s, ts, tcg_target_available_regs[itype] &
                  ~allocated_regs, preferred_regs);
    }

    ts_set_next_use(ts, op->next_use[1]);
    tcg_debug_assert(ts_val_type(ts) == TEMP_VAL_REG);
    if (IS_DEAD_ARG(0)) {
        /* Mov to a non-saved dead register makes no sense.  */
        tcg_debug_assert(NEED_SYNC_ARG(0));
        temp_store(s, ots, otype, ts->reg);
        if (IS_DEAD_ARG(1)) {
            temp_dead(s, ts);
        } else if (DO_CLOBBER_ARG(1, ts)) {
            temp_clobber(s, ts);
        }
        ts_set_next_use(ots, op->next_use[0]);
        temp_dead(s, ots);
    } else {
        if (IS_DEAD_ARG(1) && ts->kind != TEMP_FIXED) {
            /* The MOV can be suppressed.  */
            reg = ts->reg;
            temp_dead(s, ts);
        } else {
            /* Allocate the output register now, make sure to not spill
             * the input register.  */
            tcg_regset_set_reg(allocated_regs, ts->reg);
            reg = tcg_reg_alloc(s, tcg_target_available_regs[otype] &
                                ~allocated_regs, preferred_regs,
                                ots->indirect_base);
            if (!tcg_out_mov(s, otype, reg, ts->reg)) {
                /*
                 * Cross register class move not supported.
                 * Store the source register into the destination slot
                 * and leave the destination temp as TEMP_VAL_MEM.
                 */
                temp_store(s, ots, itype, ts->reg);
                ts_set_val_type(ots, TEMP_VAL_MEM);
                return;
            }
            if (DO_CLOBBER_ARG(1, ts)) {
                temp_clobber(s, ts);
            }
        }
        temp_commit_register(s, ots, reg, true);
        ts_set_next_use(ots, op->next_use[0]);
        if (NEED_SYNC_ARG(0)) {
            temp_sync(s, ots, -DO_CLOBBER_ARG(0, ots));
        } else if (DO_CLOBBER_ARG(0, ots)) {
            temp_clobber(s, ots);
        }
    }
}

/*
 * Specialized code generation for INDEX_op_dup_vec.
 */
static void tcg_reg_alloc_dup(TCGContext *s, const TCGOp *op)
{
    TCGRegSet dup_out_regs, dup_in_regs;
    TCGTemp *its, *ots;
    TCGType itype, vtype;
    intptr_t endian_fixup;
    unsigned vece;
    bool ok;
    TCGRegSet allocated_regs = s->reserved_regs;
    TCGReg reg;

    ots = arg_temp(op->args[0]);
    its = arg_temp(op->args[1]);

    /* Output temporary should be well-formed.  */
    tcg_reg_alloc_check_output(ots);

    itype = its->type;
    vece = TCGOP_VECE(op);
    vtype = TCGOP_VECL(op) + TCG_TYPE_V64;

    /* tcg_optimize() would have convert this to mov_vec.  */
    tcg_debug_assert(!(ts_val_type(its) == TEMP_VAL_CONST));

    dup_out_regs = tcg_op_defs[INDEX_op_dup_vec].args_ct[0].regs;
    dup_in_regs = tcg_op_defs[INDEX_op_dup_vec].args_ct[1].regs;

    /* Allocate the output register now, make sure to not spill
     * the input register.  */
    if (!IS_DEAD_ARG(1) && ts_val_type(its) == TEMP_VAL_REG) {
        tcg_regset_set_reg(allocated_regs, its->reg);
    }
    reg = tcg_reg_alloc(s, dup_out_regs & ~allocated_regs, op->output_pref[0],
                        ots->indirect_base);
    temp_commit_register(s, ots, reg, true);

    switch (ts_val_type(its)) {
    case TEMP_VAL_REG:
        /*
         * The dup constriaints must be broad, covering all possible VECE.
         * However, tcg_op_dup_vec() gets to see the VECE and we allow it
         * to fail, indicating that extra moves are required for that case.
         */
        if (tcg_regset_test_reg(dup_in_regs, its->reg)) {
            if (tcg_out_dup_vec(s, vtype, vece, ots->reg, its->reg)) {
                goto done;
            }
            /* Try again from memory or a vector input register.  */
        }
        if (!its->mem_coherent) {
            /*
             * The input register is not synced, and so an extra store
             * would be required to use memory.  Attempt an integer-vector
             * register move first.  We do not have a TCGRegSet for this.
             */
            if (tcg_out_mov(s, itype, ots->reg, its->reg)) {
                break;
            }
            /* Sync the temp back to its slot and load from there.  */
            temp_sync(s, its, 0);
        }
        /* fall through */

    case TEMP_VAL_MEM:
#ifdef HOST_WORDS_BIGENDIAN
        endian_fixup = itype == TCG_TYPE_I32 ? 4 : 8;
        endian_fixup -= 1 << vece;
#else
        endian_fixup = 0;
#endif
        if (tcg_out_dupm_vec(s, vtype, vece, ots->reg, its->mem_base->reg,
                             its->mem_offset + endian_fixup)) {
            goto done;
        }
        tcg_out_ld(s, itype, ots->reg, its->mem_base->reg, its->mem_offset);
        break;

    default:
        g_assert_not_reached();
    }

    /* We now have a vector input register, so dup must succeed.  */
    ok = tcg_out_dup_vec(s, vtype, vece, ots->reg, ots->reg);
    tcg_debug_assert(ok);

done:
    ts_set_next_use(its, op->next_use[1]);
    if (IS_DEAD_ARG(1)) {
        temp_dead(s, its);
    } else if (DO_CLOBBER_ARG(1, its)) {
        temp_clobber(s, its);
    }
    ts_set_next_use(ots, op->next_use[0]);
    if (NEED_SYNC_ARG(0)) {
        temp_sync(s, ots, IS_DEAD_ARG(0) - DO_CLOBBER_ARG(0, ots));
    } else {
        /* Mov to a non-saved dead register makes no sense.  */
        tcg_debug_assert(!IS_DEAD_ARG(0));
        if (DO_CLOBBER_ARG(0, ots)) {
            temp_clobber(s, ots);
        }
    }
}

static inline void temp_finalize(TCGContext *s, const TCGOp *op, uint8_t i,
                                 bool is_oarg)
{
    TCGTemp *ts = arg_temp(op->args[i]);

    ts_set_next_use(ts, op->next_use[i]);
    if (is_oarg && NEED_SYNC_ARG(i)) {
        temp_sync(s, ts, IS_DEAD_ARG(i) - DO_CLOBBER_ARG(i, ts));
    } else if (IS_DEAD_ARG(i)) {
        temp_dead(s, ts);
    } else if (DO_CLOBBER_ARG(i, ts)) {
        temp_clobber(s, ts);
    }
}

static void temp_move(TCGContext *s, TCGTemp *ts, TCGReg reg)
{
    tcg_debug_assert(ts_val_type(ts) == TEMP_VAL_REG);
    if (!tcg_out_mov(s, ts->type, reg, ts->reg)) {
        /* Cross register class move not supported. Sync the
         * temp back to its slot and load from there.  */
        temp_sync(s, ts, 0);
        tcg_out_ld(s, ts->type, reg, ts->mem_base->reg, ts->mem_offset);
    }
}

static void tcg_reg_alloc_op(TCGContext *s, const TCGOp *op)
{
    uint8_t nb_iargs, nb_oargs;
    const TCGOpDef * const def = &tcg_op_defs[op->opc];
    TCGRegSet i_allocated_regs;
    TCGRegSet o_allocated_regs;
    size_t i, k;
    TCGReg reg;
    const TCGArgConstraint *arg_ct;
    TCGTemp *ts;
    TCGArg new_args[TCG_MAX_OP_ARGS];
    BackendValType arg_types[TCG_MAX_OP_ARGS];

    nb_oargs = def->nb_oargs;
    nb_iargs = def->nb_iargs;

    /* Copy constants.  */
    memcpy(&new_args[nb_oargs + nb_iargs], &op->args[nb_oargs + nb_iargs],
           sizeof(TCGArg) * def->nb_cargs);

    i_allocated_regs = s->reserved_regs;
    o_allocated_regs = s->reserved_regs;

    /* Satisfy input constraints.  */
    for (k = 0; k < nb_iargs; k++) {
        TCGRegSet i_preferred_regs, o_preferred_regs;

        i = def->args_ct[nb_oargs + k].sort_index;
        arg_ct = &def->args_ct[i];
        ts = arg_temp(op->args[i]);

        if (ts_val_type(ts) == TEMP_VAL_CONST
            && tcg_target_const_match(ts->val, ts->type, arg_ct)) {
            /* Constant is OK for the instruction.  */
            arg_types[i] = BACKEND_CONST;
            new_args[i] = ts->val;
            continue;
        }

        i_preferred_regs = o_preferred_regs = 0;
        if (arg_ct->ialias) {
            o_preferred_regs = op->output_pref[arg_ct->alias_index];

            /*
             * If the input is readonly, then it cannot also be an
             * output and aliased to itself.  If the input is not
             * dead after the instruction, we must allocate a new
             * register and move it.
             */
            if (temp_readonly(ts) || !IS_DEAD_ARG(i)) {
                goto allocate_in_reg;
            }

            /*
             * Check if the current register has already been allocated
             * for another input aliased to an output.
             */
            if (ts_val_type(ts) == TEMP_VAL_REG) {
                reg = ts->reg;
                for (size_t k2 = 0; k2 < k; k2++) {
                    size_t i2 = def->args_ct[nb_oargs + k2].sort_index;
                    if (def->args_ct[i2].ialias && reg == new_args[i2]) {
                        goto allocate_in_reg;
                    }
                }
            }
            i_preferred_regs = o_preferred_regs;
        }

        temp_load(s, ts, arg_ct->regs & ~i_allocated_regs, i_preferred_regs);
        reg = ts->reg;

        if (!tcg_regset_test_reg(arg_ct->regs, reg)) {
    allocate_in_reg:
            /*
             * Allocate a new register matching the constraint
             * and move the temporary register into it.
             */
            temp_load(s, ts, tcg_target_available_regs[ts->type] &
                      ~i_allocated_regs, 0);
            reg = tcg_reg_alloc(s, arg_ct->regs & ~i_allocated_regs,
                                o_preferred_regs, ts->indirect_base);
            /* Nasty case where tcg_reg_alloc spills the very register
             * that `ts` uses, no move is therefore needed.  */
            if (reg != ts->reg) {
                temp_move(s, ts, reg);
            }
        }
        new_args[i] = reg;
        arg_types[i] = BACKEND_REG;
        tcg_regset_set_reg(i_allocated_regs, reg);
    }

    /* Mark dead temporaries and free the associated registers.  */
    for (i = nb_oargs; i < nb_oargs + nb_iargs; i++) {
        temp_finalize(s, op, i, false);
    }

    if (def->flags & TCG_OPF_COND_BRANCH) {
        tcg_reg_alloc_cbranch(s);
    } else if (def->flags & TCG_OPF_BB_END) {
        tcg_reg_alloc_bb_end(s);
    } else {
        if (def->flags & TCG_OPF_CALL_CLOBBER) {
            if (op->opc == INDEX_op_tlb_check ||
                op->opc == INDEX_op_itlb_check) {
                for (i = 0; i < TCG_TARGET_NB_REGS; i++) {
                    if (tcg_regset_test_reg(tcg_target_tlb_check_clobber_regs,
                                            i)) {
                        /* Liveness analysis should have ensured that temporary
                         * using registers clobbered by this op be freed.  */
                        tcg_debug_assert(!s->reg_to_temp[i]);
                    }
                }
                tcg_debug_assert(def->nb_oargs == 0);
                tcg_out_op(s, op->opc, new_args, arg_types);
                return;
            }
            for (i = 0; i < TCG_TARGET_NB_REGS; i++) {
                if (tcg_regset_test_reg(tcg_target_call_clobber_regs, i)) {
                    tcg_reg_free(s, i);
                }
            }
        }
        if (def->flags & TCG_OPF_SIDE_EFFECTS) {
            /* Sync globals if the op has side effects and might trigger
             * an exception.  */
            sync_globals(s);
        }

        /* Satisfy the output constraints.  */
        for(k = 0; k < nb_oargs; k++) {
            i = def->args_ct[k].sort_index;
            arg_ct = &def->args_ct[i];
            ts = arg_temp(op->args[i]);

            /* Output temporary should be well-formed.  */
            tcg_reg_alloc_check_output(ts);

            if (arg_ct->oalias
                && (arg_types[arg_ct->alias_index] == BACKEND_REG)) {
                reg = new_args[arg_ct->alias_index];
            } else if (arg_ct->newreg) {
                reg = tcg_reg_alloc(s, arg_ct->regs &
                                    ~(i_allocated_regs | o_allocated_regs),
                                    op->output_pref[k], ts->indirect_base);
            } else {
                reg = tcg_reg_alloc(s, arg_ct->regs & ~o_allocated_regs,
                                    op->output_pref[k], ts->indirect_base);
            }
            tcg_regset_set_reg(o_allocated_regs, reg);
            temp_commit_register(s, ts, reg, true);
            new_args[i] = reg;
        }
    }

    /* Emit instruction.  */
    if (def->flags & TCG_OPF_VECTOR) {
        tcg_out_vec_op(s, op->opc, TCGOP_VECL(op), TCGOP_VECE(op),
                       new_args, arg_types);
    } else {
        tcg_out_op(s, op->opc, new_args, arg_types);
    }

    for(i = 0; i < nb_oargs; i++) {
        temp_finalize(s, op, i, true);
    }
}

static bool tcg_reg_alloc_dup2(TCGContext *s, const TCGOp *op)
{
    /* DUP2 is not updated as with the other tcg_reg_alloc_*.  */
    g_assert_not_reached();

    TCGTemp *ots, *itsl, *itsh;
    TCGType vtype = TCGOP_VECL(op) + TCG_TYPE_V64;
    TCGRegSet allocated_regs = s->reserved_regs;
    TCGRegSet dup_out_regs = tcg_op_defs[INDEX_op_dup_vec].args_ct[0].regs;
    TCGReg reg;

    /* This opcode is only valid for 32-bit hosts, for 64-bit elements.  */
    tcg_debug_assert(TCG_TARGET_REG_BITS == 32);
    tcg_debug_assert(TCGOP_VECE(op) == MO_64);

    ots = arg_temp(op->args[0]);
    itsl = arg_temp(op->args[1]);
    itsh = arg_temp(op->args[2]);

    /* Output temporary should be well-formed.  */
    tcg_reg_alloc_check_output(ots);

    /* tcg_optimize() would have convert this to mov_vec.  */
    tcg_debug_assert(!(ts_val_type(itsl) == TEMP_VAL_CONST &&
                       ts_val_type(itsh) == TEMP_VAL_CONST));

    /* Allocate the output register now, make sure to not spill
     * the input registers.  */
    if (!IS_DEAD_ARG(1) && ts_val_type(itsl) == TEMP_VAL_REG) {
        tcg_regset_set_reg(allocated_regs, itsl->reg);
    }
    if (!IS_DEAD_ARG(2) && ts_val_type(itsh) == TEMP_VAL_REG) {
        tcg_regset_set_reg(allocated_regs, itsh->reg);
    }

    reg = tcg_reg_alloc(s, dup_out_regs & ~allocated_regs, op->output_pref[0],
                        ots->indirect_base);
    temp_commit_register(s, ots, reg, true);

    /* If the two inputs form one 64-bit value, try dupm_vec.  */
    if (itsl + 1 == itsh && itsl->base_type == TCG_TYPE_I64) {
        if (!itsl->mem_coherent) {
            temp_sync(s, itsl, 0);
        }
        if (!itsh->mem_coherent) {
            temp_sync(s, itsh, 0);
        }
#ifdef HOST_WORDS_BIGENDIAN
        TCGTemp *its = itsh;
#else
        TCGTemp *its = itsl;
#endif
        if (tcg_out_dupm_vec(s, vtype, MO_64, ots->reg,
                             its->mem_base->reg, its->mem_offset)) {
            goto done;
        }
    }

    /* Fall back to generic expansion.  */
    return false;

done:
    if (IS_DEAD_ARG(1)) {
        temp_dead(s, itsl);
    }
    if (IS_DEAD_ARG(2)) {
        temp_dead(s, itsh);
    }
    if (NEED_SYNC_ARG(0)) {
        temp_sync(s, ots, IS_DEAD_ARG(0));
    } else {
        /* Mov to a non-saved dead register makes no sense.  */
        tcg_debug_assert(!IS_DEAD_ARG(0));
    }
    return true;
}

#ifdef TCG_TARGET_STACK_GROWSUP
#define STACK_DIR(x) (-(x))
#else
#define STACK_DIR(x) (x)
#endif

static void tcg_reg_alloc_call(TCGContext *s, const TCGOp *op)
{
    const uint8_t nb_oargs = TCGOP_CALLO(op);
    const uint8_t nb_iargs = TCGOP_CALLI(op);
    uint16_t flags = op->args[nb_oargs + nb_iargs + 1];
    tcg_insn_unit *func_addr = (tcg_insn_unit *) op->args[nb_oargs + nb_iargs];
    size_t nb_regs, i;
    TCGReg reg;
    TCGTemp *ts;
    intptr_t stack_offset;
    size_t call_stack_size;

    nb_regs = ARRAY_SIZE(tcg_target_call_iarg_regs);
    if (nb_regs > nb_iargs) {
        nb_regs = nb_iargs;
    }

    /* Assign stack slots first.  */
    call_stack_size = (nb_iargs - nb_regs) * sizeof(tcg_target_long);
    call_stack_size = (call_stack_size + TCG_TARGET_STACK_ALIGN - 1) &
        ~(TCG_TARGET_STACK_ALIGN - 1);
    tcg_debug_assert(call_stack_size <= TCG_STATIC_CALL_ARGS_SIZE);

    stack_offset = TCG_TARGET_CALL_STACK_OFFSET;
    for (i = nb_regs; i < nb_iargs; i++) {
        if (!(ts = arg_temp(op->args[nb_oargs + i]))) {
            continue;
        }
#ifdef TCG_TARGET_STACK_GROWSUP
        stack_offset -= sizeof(tcg_target_long);
#endif
        temp_load(s, ts, tcg_target_available_regs[ts->type] &
                  ~s->reserved_regs, 0);
        tcg_out_st(s, ts->type, ts->reg, TCG_REG_CALL_STACK, stack_offset);
#ifndef TCG_TARGET_STACK_GROWSUP
        stack_offset += sizeof(tcg_target_long);
#endif
    }

    /* Assign input registers.  */
    for (i = 0; i < nb_regs; i++) {
        if (!(ts = arg_temp(op->args[nb_oargs + i]))) {
            continue;
        }
        reg = tcg_target_call_iarg_regs[i];

        if (ts_val_type(ts) == TEMP_VAL_REG) {
            if (ts->reg != reg) {
                tcg_reg_free(s, reg);
                temp_move(s, ts, reg);
            }
        } else {
            tcg_reg_free(s, reg);
            /* `tcg_target_call_iarg_regs[]` should not overlap with
             * each other, as well as with `s->reserved_regs`, so no
             * `allocated_regs` is needed here.  */
            temp_load(s, ts, tcg_regset_from_reg(reg), 0);
        }
    }

    /* Mark dead temporaries and free the associated registers.  */
    for (i = nb_oargs; i < nb_iargs + nb_oargs; i++) {
        temp_finalize(s, op, i, false);
    }

    /* Clobber call registers.  */
    for (i = 0; i < TCG_TARGET_NB_REGS; i++) {
        if (tcg_regset_test_reg(tcg_target_call_clobber_regs, i)) {
            tcg_reg_free(s, i);
        }
    }

    /* Save globals if they might be written by the helper, sync them if
     * they might be read.  */
    if (flags & TCG_CALL_NO_READ_GLOBALS) {
        /* Nothing to do.  */
    } else if (flags & TCG_CALL_NO_WRITE_GLOBALS) {
        sync_globals(s);
    } else {
        save_globals(s);
    }

    tcg_out_call(s, func_addr);

    /* Assign output registers and emit moves if needed.  */
    for(i = 0; i < nb_oargs; i++) {
        ts = arg_temp(op->args[i]);

        /* Output temporary should be well-formed.  */
        tcg_reg_alloc_check_output(ts);

        reg = tcg_target_call_oarg_regs[i];
        /* Input registers should always be listed in call_clobber_list,
         * and therefore should have already been freed by this time.  */
        tcg_debug_assert(s->reg_to_temp[reg] == NULL);
        temp_commit_register(s, ts, reg, true);

        temp_finalize(s, op, i, true);
    }
}

#include "tcg-target.c.inc"

#ifdef CONFIG_PROFILER

/* avoid copy/paste errors */
#define PROF_ADD(to, from, field)                       \
    do {                                                \
        (to)->field += qatomic_read(&((from)->field));  \
    } while (0)

#define PROF_MAX(to, from, field)                                       \
    do {                                                                \
        typeof((from)->field) val__ = qatomic_read(&((from)->field));   \
        if (val__ > (to)->field) {                                      \
            (to)->field = val__;                                        \
        }                                                               \
    } while (0)

/* Pass in a zero'ed @prof */
static inline
void tcg_profile_snapshot(TCGProfile *prof, bool counters, bool table)
{
    unsigned int n_ctxs = qatomic_read(&n_tcg_ctxs);
    unsigned int i;

    for (i = 0; i < n_ctxs; i++) {
        TCGContext *s = qatomic_read(&tcg_ctxs[i]);
        const TCGProfile *orig = &s->prof;

        if (counters) {
            PROF_ADD(prof, orig, cpu_exec_time);
            PROF_ADD(prof, orig, tb_count1);
            PROF_ADD(prof, orig, tb_count);
            PROF_ADD(prof, orig, op_count);
            PROF_MAX(prof, orig, op_count_max);
            PROF_ADD(prof, orig, temp_count);
            PROF_MAX(prof, orig, temp_count_max);
            PROF_ADD(prof, orig, del_op_count);
            PROF_ADD(prof, orig, code_in_len);
            PROF_ADD(prof, orig, code_out_len);
            PROF_ADD(prof, orig, search_out_len);
            PROF_ADD(prof, orig, interm_time);
            PROF_ADD(prof, orig, code_time);
            PROF_ADD(prof, orig, la_time);
            PROF_ADD(prof, orig, opt_time);
            PROF_ADD(prof, orig, restore_count);
            PROF_ADD(prof, orig, restore_time);
        }
        if (table) {
            int i;

            for (i = 0; i < NB_OPS; i++) {
                PROF_ADD(prof, orig, table_op_count[i]);
            }
        }
    }
}

#undef PROF_ADD
#undef PROF_MAX

static void tcg_profile_snapshot_counters(TCGProfile *prof)
{
    tcg_profile_snapshot(prof, true, false);
}

static void tcg_profile_snapshot_table(TCGProfile *prof)
{
    tcg_profile_snapshot(prof, false, true);
}

void tcg_dump_op_count(void)
{
    TCGProfile prof = {};
    int i;

    tcg_profile_snapshot_table(&prof);
    for (i = 0; i < NB_OPS; i++) {
        qemu_printf("%s %" PRId64 "\n", tcg_op_defs[i].name,
                    prof.table_op_count[i]);
    }
}

int64_t tcg_cpu_exec_time(void)
{
    unsigned int n_ctxs = qatomic_read(&n_tcg_ctxs);
    unsigned int i;
    int64_t ret = 0;

    for (i = 0; i < n_ctxs; i++) {
        const TCGContext *s = qatomic_read(&tcg_ctxs[i]);
        const TCGProfile *prof = &s->prof;

        ret += qatomic_read(&prof->cpu_exec_time);
    }
    return ret;
}
#else
void tcg_dump_op_count(void)
{
    qemu_printf("[TCG profiler not compiled]\n");
}

int64_t tcg_cpu_exec_time(void)
{
    error_report("%s: TCG profiler not compiled", __func__);
    exit(EXIT_FAILURE);
}
#endif

static void tcg_optimize__common(TCGContext *s, target_ulong pc)
{
#ifdef CONFIG_PROFILER
    TCGProfile *prof = &s->prof;

    qatomic_set(&prof->la_time, prof->la_time - profile_getclock());
#endif

    reachable_code_pass(s);
    liveness_pass_1(s);

    if (s->nb_indirects > 0) {
#ifdef DEBUG_DISAS
        if (unlikely(qemu_loglevel_mask(CPU_LOG_TB_OP_IND)
                     && qemu_log_in_addr_range(pc))) {
            FILE *logfile = qemu_log_lock();
            qemu_log("OP before indirect lowering:\n");
            tcg_dump_ops(s, false);
            qemu_log("\n");
            qemu_log_unlock(logfile);
        }
#endif
        /* Replace indirect temps with direct temps.  */
        if (liveness_pass_2(s)) {
            /* If changes were made, re-run liveness.  */
            liveness_pass_1(s);
        }
    }

#ifdef CONFIG_PROFILER
    qatomic_set(&prof->la_time, prof->la_time + profile_getclock());
#endif

#ifdef DEBUG_DISAS
    if (unlikely(qemu_loglevel_mask(CPU_LOG_TB_OP_OPT)
                 && qemu_log_in_addr_range(pc))) {
        FILE *logfile = qemu_log_lock();
        qemu_log("OP after optimization and liveness analysis:\n");
        tcg_dump_ops(s, true);
        qemu_log("\n");
        qemu_log_unlock(logfile);
    }
#endif
}

void tcg_pre_gen_code__cold(TCGContext *s, TranslationBlock *tb)
{
#ifdef CONFIG_PROFILER
    TCGProfile *prof = &s->prof;

    {
        int n = 0;
        TCGOp *op;

        QTAILQ_FOREACH(op, &s->ops, link) {
            n++;
        }
        qatomic_set(&prof->op_count, prof->op_count + n);
        if (n > prof->op_count_max) {
            qatomic_set(&prof->op_count_max, n);
        }

        n = s->nb_temps;
        qatomic_set(&prof->temp_count, prof->temp_count + n);
        if (n > prof->temp_count_max) {
            qatomic_set(&prof->temp_count_max, n);
        }
    }
#endif

#ifdef DEBUG_DISAS
    if (unlikely(qemu_loglevel_mask(CPU_LOG_TB_OP)
                 && qemu_log_in_addr_range(tb->pc))) {
        FILE *logfile = qemu_log_lock();
        qemu_log("OP:\n");
        tcg_dump_ops(s, false);
        qemu_log("\n");
        qemu_log_unlock(logfile);
    }
#endif

#ifdef CONFIG_DEBUG_TCG
    /* Ensure all labels referenced have been emitted.  */
    {
        TCGLabel *l;
        bool error = false;

        QSIMPLEQ_FOREACH(l, &s->labels, next) {
            if (unlikely(!l->present) && l->refs) {
                qemu_log_mask(CPU_LOG_TB_OP,
                              "$L%d referenced but not present.\n", l->id);
                error = true;
            }
        }
        assert(!error);
    }
#endif

#ifdef CONFIG_PROFILER
    qatomic_set(&prof->opt_time, prof->opt_time - profile_getclock());
#endif

    tcg_optimize(s);

#ifdef DEBUG_DISAS
    if (unlikely(qemu_loglevel_mask(CPU_LOG_TB_OP_SSA)
                 && qemu_log_in_addr_range(tb->pc))) {
        FILE *logfile = qemu_log_lock();
        qemu_log("OP before liveness analysis:\n");
        tcg_dump_ops(s, false);
        qemu_log("\n");
        qemu_log_unlock(logfile);
    }
#endif

#ifdef CONFIG_PROFILER
    qatomic_set(&prof->opt_time, prof->opt_time + profile_getclock());
#endif

    tcg_optimize__common(s, tb->pc);
}

int tcg_gen_code(TCGContext *s, TranslationBlock *tb)
{
#ifdef CONFIG_PROFILER
    TCGProfile *prof = &s->prof;
#endif
    int i, num_insns;
    TCGOp *op;

    /* Prepare for machine code generation.  */
    tb->jmp_reset_offset[0] = TB_JMP_RESET_OFFSET_INVALID;
    tb->jmp_reset_offset[1] = TB_JMP_RESET_OFFSET_INVALID;
    s->tb_jmp_reset_offset = tb->jmp_reset_offset;
    if (TCG_TARGET_HAS_direct_jump) {
        s->tb_jmp_insn_offset = tb->jmp_target_arg;
        s->tb_jmp_target_addr = NULL;
    } else {
        s->tb_jmp_insn_offset = NULL;
        s->tb_jmp_target_addr = tb->jmp_target_arg;
    }

    tcg_reg_alloc_start(s);

    s->code_buf = tb->tc.ptr;
    s->code_ptr = tb->tc.ptr;

#ifdef TCG_TARGET_NEED_SLOW_PATH_LABELS
    QSIMPLEQ_INIT(&s->slow_path_labels);
#endif
#ifdef TCG_TARGET_NEED_POOL_LABELS
    s->pool_labels = NULL;
#endif

    num_insns = -1;
    QTAILQ_FOREACH(op, &s->ops, link) {
        TCGOpcode opc = op->opc;

#ifdef CONFIG_PROFILER
        qatomic_set(&prof->table_op_count[opc], prof->table_op_count[opc] + 1);
#endif

        s->current_insn--;
        switch (opc) {
        case INDEX_op_mov_i32:
        case INDEX_op_mov_i64:
        case INDEX_op_mov_vec:
            tcg_reg_alloc_mov(s, op);
            break;
        case INDEX_op_dup_vec:
            tcg_reg_alloc_dup(s, op);
            break;
        case INDEX_op_insn_start:
            if (num_insns >= 0) {
                size_t off = tcg_current_code_size(s);
                s->gen_insn_end_off[num_insns] = off;
                /* Assert that we do not overflow our stored offset.  */
                assert(s->gen_insn_end_off[num_insns] == off);
            } else {
                tb->prologue_offset = tcg_current_code_size(s);
            }
            num_insns++;
            for (i = 0; i < TARGET_INSN_START_WORDS; ++i) {
                target_ulong a;
#if TARGET_LONG_BITS > TCG_TARGET_REG_BITS
                a = deposit64(op->args[i * 2], 32, 32, op->args[i * 2 + 1]);
#else
                a = op->args[i];
#endif
                s->gen_insn_data[num_insns][i] = a;
            }
            break;
        case INDEX_op_discard:
            ts_set_next_use(arg_temp(op->args[0]), op->next_use[0]);
            temp_dead(s, arg_temp(op->args[0]));
            break;
        case INDEX_op_set_label:
            tcg_reg_alloc_bb_end(s);
            tcg_out_label(s, arg_label(op->args[0]), s->code_ptr);
            break;
        case INDEX_op_call:
            tcg_reg_alloc_call(s, op);
            break;
        case INDEX_op_dup2_vec:
            if (tcg_reg_alloc_dup2(s, op)) {
                break;
            }
            goto do_default;
        case INDEX_op_side_effect:
            sync_globals(s);
            break;
        default:
        do_default:
            /* Sanity check that we've not introduced any unhandled opcodes. */
            tcg_debug_assert(tcg_op_supported_by_backend(opc));
            /* Note: in order to speed up the code, it would be much
               faster to have specialized register allocator functions for
               some common argument patterns */
            tcg_reg_alloc_op(s, op);
            break;
        }
#ifdef CONFIG_DEBUG_TCG
        check_regs(s);
#endif
        /* Test for (pending) buffer overflow.  The assumption is that any
           one operation beginning below the high water mark cannot overrun
           the buffer completely.  Thus we can test for overflow after
           generating code without having to check during generation.  */
        if (unlikely((void *)s->code_ptr > s->code_gen_highwater)) {
            return -1;
        }
        /* Test for TB overflow, as seen by gen_insn_end_off.  */
        if (unlikely(tcg_current_code_size(s) > UINT16_MAX)) {
            return -2;
        }
    }
    if (!s->trace) {
        tcg_debug_assert(num_insns + 1 == tb->icount);
    } else {
        tb->icount = num_insns + 1;
    }
    s->gen_insn_end_off[num_insns] = tcg_current_code_size(s);

    /* Generate TB finalization at the end of block */
#ifdef TCG_TARGET_NEED_SLOW_PATH_LABELS
    i = tcg_out_slow_path_finalize(s);
    if (i < 0) {
        return i;
    }
#endif
#ifdef TCG_TARGET_NEED_POOL_LABELS
    i = tcg_out_pool_finalize(s);
    if (i < 0) {
        return i;
    }
#endif
    if (!tcg_resolve_relocs(s)) {
        return -2;
    }

    /* flush instruction cache */
    flush_icache_range((uintptr_t)s->code_buf, (uintptr_t)s->code_ptr);

    tb->tc.size = tcg_current_code_size(s);
    return encode_search(tb, tb->tc.ptr + tb->tc.size);
}

void tcg_tracer_reset(void)
{
    if (!tcg_ctx->trace) {
        return;
    }
    tcg_ctx->trace = false;
    /* Resetting HEAD_TB suffices to do the clean up, everything else will
     * be re-initialized the next time TCG enters trace recording mode.  */
    if (tcg_ctx->head_tb) {
        /* Do not waste if not explicitly nullified (which express the intent
         * of forbidding further recording starting from here, as its counter
         * has expired).  */
        qatomic_set(&tcg_ctx->head_tb->exec_count, PROFILE_THRESHOLD - 5);
        tcg_ctx->head_tb = NULL;
    }
}

static inline bool is_decent_tb_for_tracing(const TranslationBlock *tb)
{
    uint32_t cflags = tb_cflags(tb);
    return likely((cflags & CF_MONOLITHIC) && // !(cflags & CF_BLACKLIST) &&
                  (tb->page_addr[0] != -1));
}

/* Return true if the trace recording mode should continue,
 * otherwise false with IR sequence ready to do codegen.  */
bool tcg_tracer_retranslate_tb(CPUState *cpu, TranslationBlock *tb)
{
    TCGContext *s = tcg_ctx;
    uint16_t size = tb->size, icount = tb->icount;

    /* Use s->head_tb to indicate whether or not the tracer state has been
     * initialized, note that its being nonnull stands for "IR sequence is
     * valid, please do codegen", so be careful when write to it.  */
    if (!s->head_tb) {
        if (!is_decent_tb_for_tracing(tb)) {
            return false;
        }
        s->head_tb = tb;
        memset(&s->cont, 0, sizeof(s->cont));
        g_hash_table_remove_all(s->tb_set);
        tcg_func_start(s);
        /* CF_BAILOUT trace doesn't need a interrupt checking stub, with reason
         * similar to that of CF_BAILOUT_1 TB:
         * 1. Trace recording must have stopped before, as CF_BAILOUT trace is
         *    side-exit of some existing trace. No need to worry about tracing
         *    into existing traces.
         * 2. CF_BAILOUT traces themselves can't form loop.
         * This makes us able to find "CALL restore_state_from_bailout" at the
         * very entry of the trace, whose parameter needs to be updated.  */
        if (!(tb_cflags(tb) & CF_BAILOUT_MASK)) {
            /* It doesn't matter which TB we are using.  */
            tcg_debug_assert(!(tb_cflags(tb) & CF_USE_ICOUNT));
            gen_tb_start(tb);
        }
        /* Re-translate the incoming TB, using !monolithic QEMU_{LD, ST}.  */
        s->tb_cflags = tb_cflags(tb) & ~(CF_MONOLITHIC | CF_BAILOUT_MASK);
    } else {
#ifdef CONFIG_DEBUG_TCG
        /* To prevent previously issued GOTO_TB from disturbing this one.  */
        s->goto_tb_issue_mask = 0;
#endif
    }

    /* Reject the TB if:
     * 1. The TB is already a trace head or has been blacklisted, or isn't
     *    backed by ordinary RAM memory area, i.e. not decent.
     * 2. CS_BASE or FLAGS differ from that of the head TB, given that any
     *    previous EXIT_TB(0) would have already terminated the trace, it's
     *    quite weird that this should happen. Known exception is related
     *    to RISC-V mark_fs_dirty().
     * 3. Loop back to existing TB collected in the trace is detected.  */
    if (!is_decent_tb_for_tracing(tb) ||
        tb->cs_base != s->head_tb->cs_base || tb->flags != s->head_tb->flags ||
        !g_hash_table_add(s->tb_set, tb)) {
        /* XXX: Unconditional constant lookup_tb_ptr may be substituted by
         * iTLB checking stub and a direct jump (GOTO_TB + EXIT_TB maybe),
         * if the target is legal. This may help if the target is entry of
         * a function call and has been traced.  */
        goto done_trace_recording;
    }
    /* This probably should be the same.  */
    tcg_debug_assert(s->tb_cflags == (tb_cflags(tb) & ~CF_MONOLITHIC));

    tcg_debug_assert((s->cpu = cpu) == current_cpu);
    gen_intermediate_code(cpu, tb, tb->icount);
    s->cpu = NULL;
    /* These probably should not be changed during tracing.  */
    tcg_debug_assert(tb->size == size && tb->icount == icount);

    /* Adapt previous TB epilogue to the newly recorded TB.  */
    tcg_opt_prune_previous_exit_stub(s, tb);

    /* Trace has reached to its length limit.  */
    if (g_hash_table_size(s->tb_set) == TRACE_LENGTH_THRESHOLD) {
        goto done_trace_recording;
    }
    return tcg_optimize__warm(s);

done_trace_recording:
    tcg_optimize__whatever_is_left(s, &s->cont);
    return false;
}

TranslationBlock *tcg_tracer_commit_trace(void)
{
    TCGContext *s = tcg_ctx;
    TranslationBlock *tb = NULL;

    tcg_debug_assert(tcg_ctx->trace);

    if (unlikely(!s->head_tb)) {
        goto exit_turn_off_trace_recording;
    } else if (s->cont.op_start) {
        tcg_optimize__whatever_is_left(s, &s->cont);
    }
    g_assert_not_reached();

exit_turn_off_trace_recording:
    s->trace = false;
    return tb;
}

#ifdef CONFIG_PROFILER
void tcg_dump_info(void)
{
    TCGProfile prof = {};
    const TCGProfile *s;
    int64_t tb_count;
    int64_t tb_div_count;
    int64_t tot;

    tcg_profile_snapshot_counters(&prof);
    s = &prof;
    tb_count = s->tb_count;
    tb_div_count = tb_count ? tb_count : 1;
    tot = s->interm_time + s->code_time;

    qemu_printf("JIT cycles          %" PRId64 " (%0.3f s at 2.4 GHz)\n",
                tot, tot / 2.4e9);
    qemu_printf("translated TBs      %" PRId64 " (aborted=%" PRId64
                " %0.1f%%)\n",
                tb_count, s->tb_count1 - tb_count,
                (double)(s->tb_count1 - s->tb_count)
                / (s->tb_count1 ? s->tb_count1 : 1) * 100.0);
    qemu_printf("avg ops/TB          %0.1f max=%d\n",
                (double)s->op_count / tb_div_count, s->op_count_max);
    qemu_printf("deleted ops/TB      %0.2f\n",
                (double)s->del_op_count / tb_div_count);
    qemu_printf("avg temps/TB        %0.2f max=%d\n",
                (double)s->temp_count / tb_div_count, s->temp_count_max);
    qemu_printf("avg host code/TB    %0.1f\n",
                (double)s->code_out_len / tb_div_count);
    qemu_printf("avg search data/TB  %0.1f\n",
                (double)s->search_out_len / tb_div_count);

    qemu_printf("cycles/op           %0.1f\n",
                s->op_count ? (double)tot / s->op_count : 0);
    qemu_printf("cycles/in byte      %0.1f\n",
                s->code_in_len ? (double)tot / s->code_in_len : 0);
    qemu_printf("cycles/out byte     %0.1f\n",
                s->code_out_len ? (double)tot / s->code_out_len : 0);
    qemu_printf("cycles/search byte     %0.1f\n",
                s->search_out_len ? (double)tot / s->search_out_len : 0);
    if (tot == 0) {
        tot = 1;
    }
    qemu_printf("  gen_interm time   %0.1f%%\n",
                (double)s->interm_time / tot * 100.0);
    qemu_printf("  gen_code time     %0.1f%%\n",
                (double)s->code_time / tot * 100.0);
    qemu_printf("optim./code time    %0.1f%%\n",
                (double)s->opt_time / (s->code_time ? s->code_time : 1)
                * 100.0);
    qemu_printf("liveness/code time  %0.1f%%\n",
                (double)s->la_time / (s->code_time ? s->code_time : 1) * 100.0);
    qemu_printf("cpu_restore count   %" PRId64 "\n",
                s->restore_count);
    qemu_printf("  avg cycles        %0.1f\n",
                s->restore_count ? (double)s->restore_time / s->restore_count : 0);
}
#else
void tcg_dump_info(void)
{
    qemu_printf("[TCG profiler not compiled]\n");
}
#endif

#ifdef ELF_HOST_MACHINE
/* In order to use this feature, the backend needs to do three things:

   (1) Define ELF_HOST_MACHINE to indicate both what value to
       put into the ELF image and to indicate support for the feature.

   (2) Define tcg_register_jit.  This should create a buffer containing
       the contents of a .debug_frame section that describes the post-
       prologue unwind info for the tcg machine.

   (3) Call tcg_register_jit_int, with the constructed .debug_frame.
*/

/* Begin GDB interface.  THE FOLLOWING MUST MATCH GDB DOCS.  */
typedef enum {
    JIT_NOACTION = 0,
    JIT_REGISTER_FN,
    JIT_UNREGISTER_FN
} jit_actions_t;

struct jit_code_entry {
    struct jit_code_entry *next_entry;
    struct jit_code_entry *prev_entry;
    const void *symfile_addr;
    uint64_t symfile_size;
};

struct jit_descriptor {
    uint32_t version;
    uint32_t action_flag;
    struct jit_code_entry *relevant_entry;
    struct jit_code_entry *first_entry;
};

void __jit_debug_register_code(void) __attribute__((noinline));
void __jit_debug_register_code(void)
{
    asm("");
}

/* Must statically initialize the version, because GDB may check
   the version before we can set it.  */
struct jit_descriptor __jit_debug_descriptor = { 1, 0, 0, 0 };

/* End GDB interface.  */

static int find_string(const char *strtab, const char *str)
{
    const char *p = strtab + 1;

    while (1) {
        if (strcmp(p, str) == 0) {
            return p - strtab;
        }
        p += strlen(p) + 1;
    }
}

static void tcg_register_jit_int(void *buf_ptr, size_t buf_size,
                                 const void *debug_frame,
                                 size_t debug_frame_size)
{
    struct __attribute__((packed)) DebugInfo {
        uint32_t  len;
        uint16_t  version;
        uint32_t  abbrev;
        uint8_t   ptr_size;
        uint8_t   cu_die;
        uint16_t  cu_lang;
        uintptr_t cu_low_pc;
        uintptr_t cu_high_pc;
        uint8_t   fn_die;
        char      fn_name[16];
        uintptr_t fn_low_pc;
        uintptr_t fn_high_pc;
        uint8_t   cu_eoc;
    };

    struct ElfImage {
        ElfW(Ehdr) ehdr;
        ElfW(Phdr) phdr;
        ElfW(Shdr) shdr[7];
        ElfW(Sym)  sym[2];
        struct DebugInfo di;
        uint8_t    da[24];
        char       str[80];
    };

    struct ElfImage *img;

    static const struct ElfImage img_template = {
        .ehdr = {
            .e_ident[EI_MAG0] = ELFMAG0,
            .e_ident[EI_MAG1] = ELFMAG1,
            .e_ident[EI_MAG2] = ELFMAG2,
            .e_ident[EI_MAG3] = ELFMAG3,
            .e_ident[EI_CLASS] = ELF_CLASS,
            .e_ident[EI_DATA] = ELF_DATA,
            .e_ident[EI_VERSION] = EV_CURRENT,
            .e_type = ET_EXEC,
            .e_machine = ELF_HOST_MACHINE,
            .e_version = EV_CURRENT,
            .e_phoff = offsetof(struct ElfImage, phdr),
            .e_shoff = offsetof(struct ElfImage, shdr),
            .e_ehsize = sizeof(ElfW(Shdr)),
            .e_phentsize = sizeof(ElfW(Phdr)),
            .e_phnum = 1,
            .e_shentsize = sizeof(ElfW(Shdr)),
            .e_shnum = ARRAY_SIZE(img->shdr),
            .e_shstrndx = ARRAY_SIZE(img->shdr) - 1,
#ifdef ELF_HOST_FLAGS
            .e_flags = ELF_HOST_FLAGS,
#endif
#ifdef ELF_OSABI
            .e_ident[EI_OSABI] = ELF_OSABI,
#endif
        },
        .phdr = {
            .p_type = PT_LOAD,
            .p_flags = PF_X,
        },
        .shdr = {
            [0] = { .sh_type = SHT_NULL },
            /* Trick: The contents of code_gen_buffer are not present in
               this fake ELF file; that got allocated elsewhere.  Therefore
               we mark .text as SHT_NOBITS (similar to .bss) so that readers
               will not look for contents.  We can record any address.  */
            [1] = { /* .text */
                .sh_type = SHT_NOBITS,
                .sh_flags = SHF_EXECINSTR | SHF_ALLOC,
            },
            [2] = { /* .debug_info */
                .sh_type = SHT_PROGBITS,
                .sh_offset = offsetof(struct ElfImage, di),
                .sh_size = sizeof(struct DebugInfo),
            },
            [3] = { /* .debug_abbrev */
                .sh_type = SHT_PROGBITS,
                .sh_offset = offsetof(struct ElfImage, da),
                .sh_size = sizeof(img->da),
            },
            [4] = { /* .debug_frame */
                .sh_type = SHT_PROGBITS,
                .sh_offset = sizeof(struct ElfImage),
            },
            [5] = { /* .symtab */
                .sh_type = SHT_SYMTAB,
                .sh_offset = offsetof(struct ElfImage, sym),
                .sh_size = sizeof(img->sym),
                .sh_info = 1,
                .sh_link = ARRAY_SIZE(img->shdr) - 1,
                .sh_entsize = sizeof(ElfW(Sym)),
            },
            [6] = { /* .strtab */
                .sh_type = SHT_STRTAB,
                .sh_offset = offsetof(struct ElfImage, str),
                .sh_size = sizeof(img->str),
            }
        },
        .sym = {
            [1] = { /* code_gen_buffer */
                .st_info = ELF_ST_INFO(STB_GLOBAL, STT_FUNC),
                .st_shndx = 1,
            }
        },
        .di = {
            .len = sizeof(struct DebugInfo) - 4,
            .version = 2,
            .ptr_size = sizeof(void *),
            .cu_die = 1,
            .cu_lang = 0x8001,  /* DW_LANG_Mips_Assembler */
            .fn_die = 2,
            .fn_name = "code_gen_buffer"
        },
        .da = {
            1,          /* abbrev number (the cu) */
            0x11, 1,    /* DW_TAG_compile_unit, has children */
            0x13, 0x5,  /* DW_AT_language, DW_FORM_data2 */
            0x11, 0x1,  /* DW_AT_low_pc, DW_FORM_addr */
            0x12, 0x1,  /* DW_AT_high_pc, DW_FORM_addr */
            0, 0,       /* end of abbrev */
            2,          /* abbrev number (the fn) */
            0x2e, 0,    /* DW_TAG_subprogram, no children */
            0x3, 0x8,   /* DW_AT_name, DW_FORM_string */
            0x11, 0x1,  /* DW_AT_low_pc, DW_FORM_addr */
            0x12, 0x1,  /* DW_AT_high_pc, DW_FORM_addr */
            0, 0,       /* end of abbrev */
            0           /* no more abbrev */
        },
        .str = "\0" ".text\0" ".debug_info\0" ".debug_abbrev\0"
               ".debug_frame\0" ".symtab\0" ".strtab\0" "code_gen_buffer",
    };

    /* We only need a single jit entry; statically allocate it.  */
    static struct jit_code_entry one_entry;

    uintptr_t buf = (uintptr_t)buf_ptr;
    size_t img_size = sizeof(struct ElfImage) + debug_frame_size;
    DebugFrameHeader *dfh;

    img = g_malloc(img_size);
    *img = img_template;

    img->phdr.p_vaddr = buf;
    img->phdr.p_paddr = buf;
    img->phdr.p_memsz = buf_size;

    img->shdr[1].sh_name = find_string(img->str, ".text");
    img->shdr[1].sh_addr = buf;
    img->shdr[1].sh_size = buf_size;

    img->shdr[2].sh_name = find_string(img->str, ".debug_info");
    img->shdr[3].sh_name = find_string(img->str, ".debug_abbrev");

    img->shdr[4].sh_name = find_string(img->str, ".debug_frame");
    img->shdr[4].sh_size = debug_frame_size;

    img->shdr[5].sh_name = find_string(img->str, ".symtab");
    img->shdr[6].sh_name = find_string(img->str, ".strtab");

    img->sym[1].st_name = find_string(img->str, "code_gen_buffer");
    img->sym[1].st_value = buf;
    img->sym[1].st_size = buf_size;

    img->di.cu_low_pc = buf;
    img->di.cu_high_pc = buf + buf_size;
    img->di.fn_low_pc = buf;
    img->di.fn_high_pc = buf + buf_size;

    dfh = (DebugFrameHeader *)(img + 1);
    memcpy(dfh, debug_frame, debug_frame_size);
    dfh->fde.func_start = buf;
    dfh->fde.func_len = buf_size;

#ifdef DEBUG_JIT
    /* Enable this block to be able to debug the ELF image file creation.
       One can use readelf, objdump, or other inspection utilities.  */
    {
        FILE *f = fopen("/tmp/qemu.jit", "w+b");
        if (f) {
            if (fwrite(img, img_size, 1, f) != img_size) {
                /* Avoid stupid unused return value warning for fwrite.  */
            }
            fclose(f);
        }
    }
#endif

    one_entry.symfile_addr = img;
    one_entry.symfile_size = img_size;

    __jit_debug_descriptor.action_flag = JIT_REGISTER_FN;
    __jit_debug_descriptor.relevant_entry = &one_entry;
    __jit_debug_descriptor.first_entry = &one_entry;
    __jit_debug_register_code();
}
#else
/* No support for the feature.  Provide the entry point expected by exec.c,
   and implement the internal function we declared earlier.  */

static void tcg_register_jit_int(void *buf, size_t size,
                                 const void *debug_frame,
                                 size_t debug_frame_size)
{
}

void tcg_register_jit(void *buf, size_t buf_size)
{
}
#endif /* ELF_HOST_MACHINE */

#if !TCG_TARGET_MAYBE_vec
void tcg_expand_vec_op(TCGOpcode o, TCGType t, unsigned e, TCGArg a0, ...)
{
    g_assert_not_reached();
}
#endif

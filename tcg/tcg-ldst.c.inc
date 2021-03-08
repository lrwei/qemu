/*
 * TCG Backend Data: load-store optimization only.
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

typedef struct TCGLabelQemuLdst {
    bool is_ld;             /* qemu_ld: true, qemu_st: false */
    TCGMemOpIdx oi;
    TCGType type;           /* result type of a load */
    TCGReg addrlo_reg;      /* reg index for low word of guest virtual addr */
    TCGReg addrhi_reg;      /* reg index for high word of guest virtual addr */
    TCGReg datalo_reg;      /* reg index for low word to be loaded or stored */
    TCGReg datahi_reg;      /* reg index for high word to be loaded or stored */
} TCGLabelQemuLdst;

typedef struct TCGLabelTlbCheck {
    TCGArg addr;
    BackendValType addr_type;
    TCGMemOpIdx _oi;
} TCGLabelTlbCheck;

typedef struct TCGLabelGuard {
#ifdef CONFIG_DEBUG_TCG
    TCGReg arg;
    TCGReg entry;
    intptr_t offset;
#endif
} TCGLabelGuard;

typedef enum TCGLabelSlowPathType {
    QemuLdst,
    TlbCheck,
    Guard,
} TCGLabelSlowPathType;

typedef struct TCGLabelSlowPath {
    TCGLabelSlowPathType type;
    tcg_insn_unit *raddr;
    /* Oversized guest are not supported, once again.  */
    tcg_insn_unit *label_ptr;
    union {
        TCGLabelQemuLdst *ldst;
        TCGLabelTlbCheck *tlbck;
        TCGLabelGuard *guard;
    };
    QSIMPLEQ_ENTRY(TCGLabelSlowPath) next;
} TCGLabelSlowPath;


/*
 * Generate TB finalization at the end of block
 */

static bool tcg_out_qemu_ld_slow_path(TCGContext *s, TCGLabelSlowPath *spl);
static bool tcg_out_qemu_st_slow_path(TCGContext *s, TCGLabelSlowPath *spl);
static bool tcg_out_tlb_check_slow_path(TCGContext *s, TCGLabelSlowPath *spl);
static bool tcg_out_guard_slow_path(TCGContext *s, TCGLabelSlowPath *spl);

static bool tcg_dispatch_slow_path_label(TCGContext *s, TCGLabelSlowPath *spl)
{
    switch (spl->type) {
    case QemuLdst:
        return spl->ldst->is_ld
               ? tcg_out_qemu_ld_slow_path(s, spl)
               : tcg_out_qemu_st_slow_path(s, spl);
    case TlbCheck:
        return tcg_out_tlb_check_slow_path(s, spl);
    case Guard:
        return tcg_out_guard_slow_path(s, spl);
    default:
        g_assert_not_reached();
    }
}

static int tcg_out_slow_path_finalize(TCGContext *s)
{
    TCGLabelSlowPath *spl;

    /* Dispatch slow paths.  */
    QSIMPLEQ_FOREACH(spl, &s->slow_path_labels, next) {
        if (!tcg_dispatch_slow_path_label(s, spl)) {
            return -2;
        }

        /* Test for (pending) buffer overflow.  The assumption is that any
           one operation beginning below the high water mark cannot overrun
           the buffer completely.  Thus we can test for overflow after
           generating code without having to check during generation.  */
        if (unlikely((void *)s->code_ptr > s->code_gen_highwater)) {
            return -1;
        }
    }
    return 0;
}

/*
 * Allocate a new TCGLabelSlowPath entry.
 */

static inline TCGLabelSlowPath *new_slow_path_label(TCGContext *s,
                                                    tcg_insn_unit *raddr,
                                                    tcg_insn_unit *label_ptr)
{
    TCGLabelSlowPath *spl = tcg_malloc(sizeof(*spl));

    _Static_assert(TCG_TARGET_REG_BITS == 64);
    spl->raddr = raddr;
    spl->label_ptr = label_ptr;
    QSIMPLEQ_INSERT_TAIL(&s->slow_path_labels, spl, next);
    return spl;
}

/*
 * Allocate a new, non-abstact TCGLabelSlowPath entry.
 */

#define DEFINE_NEW_LABEL_FUNC(subtype, field)                                  \
static inline TCGLabel##subtype *new_##field##_label(TCGContext *s,            \
                                                     tcg_insn_unit *raddr,     \
                                                     tcg_insn_unit *label_ptr) \
{                                                                              \
    TCGLabelSlowPath *spl = new_slow_path_label(s, raddr, label_ptr);          \
    TCGLabel##subtype *l = tcg_malloc(sizeof(*l));                             \
                                                                               \
    spl->type = subtype;                                                       \
    spl->field = l;                                                            \
    return l;                                                                  \
}

DEFINE_NEW_LABEL_FUNC(QemuLdst, ldst)
DEFINE_NEW_LABEL_FUNC(TlbCheck, tlbck)
DEFINE_NEW_LABEL_FUNC(Guard, guard)

#undef DEFINE_NEW_LABEL_FUNC

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
    TCGMemOpIdx _oi;    /* Pack of IS_LOAD, MEMOP and MEM_INDEX.  */
    TCGType type;       /* Type of result, used only by QEMU_LD.  */
    TCGReg data_reg;    /* Register for data to be loaded or stored.  */
    TCGReg addr_reg;    /* Register for guest virtual address.  */
} TCGLabelQemuLdst;

typedef struct TCGLabelTlbCheck {
    TCGMemOpIdx _oi;
    BackendValType addr_type;
    TCGArg addr;
} TCGLabelTlbCheck;

typedef enum TCGLabelSlowPathType {
    QemuLdst,
    TlbCheck,
} TCGLabelSlowPathType;

typedef struct TCGLabelSlowPath {
    TCGLabelSlowPathType type;
    tcg_insn_unit *raddr;
    /* Oversized guest are not supported, once again.  */
    tcg_insn_unit *label_ptr;
    union {
        TCGLabelQemuLdst *ldst;
        TCGLabelTlbCheck *tlb_check;
    };
    QSIMPLEQ_ENTRY(TCGLabelSlowPath) next;
} TCGLabelSlowPath;


/*
 * Generate TB finalization at the end of block
 */

static bool tcg_out_qemu_ld_slow_path(TCGContext *s, TCGLabelSlowPath *spl);
static bool tcg_out_qemu_st_slow_path(TCGContext *s, TCGLabelSlowPath *spl);
static bool tcg_out_tlb_check_slow_path(TCGContext *s, TCGLabelSlowPath *spl);

static bool tcg_dispatch_slow_path_label(TCGContext *s, TCGLabelSlowPath *spl)
{
    switch (spl->type) {
    case QemuLdst:
        return !!(spl->ldst->_oi & _OI_LOAD)
               ? tcg_out_qemu_ld_slow_path(s, spl)
               : tcg_out_qemu_st_slow_path(s, spl);
    case TlbCheck:
        return tcg_out_tlb_check_slow_path(s, spl);
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

    spl->raddr = raddr;
    spl->label_ptr = label_ptr;
    QSIMPLEQ_INSERT_TAIL(&s->slow_path_labels, spl, next);
    return spl;
}

/*
 * Allocate a new, non-abstract TCGLabelSlowPath entry.
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
DEFINE_NEW_LABEL_FUNC(TlbCheck, tlb_check)

#undef DEFINE_NEW_LABEL_FUNC

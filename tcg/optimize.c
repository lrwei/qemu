/*
 * Optimizations for Tiny Code Generator for QEMU
 *
 * Copyright (c) 2010 Samsung Electronics.
 * Contributed by Kirill Batuzov <batuzovk@ispras.ru>
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
#include "tcg/tcg-op.h"
#include "exec/exec-all.h"

#define CASE_OP_32_64(x)                        \
        glue(glue(case INDEX_op_, x), _i32):    \
        glue(glue(case INDEX_op_, x), _i64)

#define CASE_OP_32_64_VEC(x)                    \
        glue(glue(case INDEX_op_, x), _i32):    \
        glue(glue(case INDEX_op_, x), _i64):    \
        glue(glue(case INDEX_op_, x), _vec)

#if TCG_TARGET_REG_BITS != 64
#error Supporting OVERSIZED GUEST is too heavy a mental burden for      \
       someone who worries about his master degree every day. So,       \
       his program simply refuse to compile.
#endif

#if TARGET_LONG_BITS == 32
#define INDEX_op_add_tl     INDEX_op_add_i32
#define INDEX_op_and_tl     INDEX_op_and_i32
#else
#define INDEX_op_add_tl     INDEX_op_add_i64
#define INDEX_op_and_tl     INDEX_op_and_i64
#endif

/* General explanation of how input IR is converted to SSA-form:
 *
 * 1. The INDIRECTION of a VARIABLE is recorded in TCGTemp::state field, its
 *    being zero means that the VAIRABLE hasn't been initialized.
 * 2. For CANONICAL (and only CANONICAL) VARIABLE, TCGTemp::state_ptr holds
 *    the information of its VALUE, i.e. TempOptInfo.
 * 3. Due to TCG frontends' not enforcing SSA-form of codegen, VARIABLE that
 *    is already CANONICAL can also be modified. As a result, tcg_optimize()
 *    will take rewrite to CANONICAL VARIABLE as modification of INDIRECTION,
 *    and remove the redefining-OP, updation to CANONICAL VARIABLE only take
 *    effect through copy propagation which examines the INDIRECTION.  */

typedef struct TempOptInfo {
    uint64_t mask;
} TempOptInfo;

static bool ts_is_const(TCGTemp *ts)
{
    return ts->kind == TEMP_CONST;
}

static uint64_t ts_value(TCGTemp *ts)
{
    tcg_debug_assert(ts_is_const(ts));
    return ts->val;
}

static bool ts_is_initialized(TCGTemp *ts)
{
    return !!ts->state;
}

static bool ts_is_canonical(TCGTemp *ts)
{
    bool ret = !!ts->state_ptr;

    /* CANONICAL VARIABLE must also be INITIALIZED.  */
    tcg_debug_assert(!ret || ts_is_initialized(ts));
    return ret;
}

static TCGTemp *ts_indirection(TCGTemp *ts)
{
    TCGTemp *indirection = (TCGTemp *) ts->state;

    tcg_debug_assert(ts_is_initialized(ts));
    tcg_debug_assert(ts_is_canonical(indirection));
    return indirection;
}

static void ts_set_indirection(TCGTemp *ts, TCGTemp *indirection)
{
    tcg_debug_assert(!indirection || ts->type == indirection->type);
    ts->state = (uintptr_t) indirection;
}

static TempOptInfo *ts_info(TCGTemp *ts)
{
    tcg_debug_assert(ts_is_canonical(ts));
    return ts->state_ptr;
}

static void init_ts_info(TCGTemp *ts, TCGOp *op)
{
    TempOptInfo *info;

    /* CANONICAL VARIABLE can't be GLOBALs or LOCALs, as they serve more
     * as memory locations, and in some sense PHIs, but not VARIABLEs.  */
    tcg_debug_assert(!temp_phi(ts));

    /* Either a read-only temporary with NULL defining op, or a TEMP_NORMAL
     * with valid definition.  */
    tcg_debug_assert(!!op ^ temp_readonly(ts));

    /* CANONICAL VARIABLEs are never re-initialized.  */
    tcg_debug_assert(!ts_is_canonical(ts));

    ts_set_indirection(ts, ts);
    ts->state_ptr = info = tcg_malloc(sizeof(TempOptInfo));

    if (ts_is_const(ts)) {
        info->mask = ts_value(ts);
        if (TCG_TARGET_REG_BITS > 32 && ts->type == TCG_TYPE_I32) {
            /* High bits of a 32-bit quantity are garbage.  */
            info->mask |= ~0xffffffffull;
        }
    } else {
        info->mask = -1;
        if (op) {
            ts->defining_op = op;
        }
    }
}

static void ts_set_uninitialized(TCGTemp *ts)
{
    ts_set_indirection(ts, NULL);
    ts->state_ptr = NULL;
}

static TCGTemp *tcg_opt_temp_new(TCGType type)
{
    TCGTemp *ts = tcg_temp_new_internal(type, TEMP_NORMAL);
    ts_set_uninitialized(ts);
    return ts;
}

static TCGArg tcg_opt_constant_new(TCGType type, int64_t value)
{
    TCGTemp *ts;

    /* Given that tcg_temp_alloc() no longer clears the whole TCGTemp, one
     * has to reset critial fields manually. See also tcg_opt_temp_new().  */
    if (tcg_constant_internal(type, value, &ts)) {
        ts_set_uninitialized(ts);
    }
    if (!ts_is_initialized(ts)) {
        init_ts_info(ts, NULL);
    }
    return temp_arg(ts);
}

static TCGOpcode type_to_mov_opc(TCGType type)
{
    switch (type) {
    case TCG_TYPE_I32:
        return INDEX_op_mov_i32;
    case TCG_TYPE_I64:
        return INDEX_op_mov_i64;
    default:
        return INDEX_op_mov_vec;
    }
}

static void init_ots_info(TCGOp *op, size_t idx)
{
    TCGTemp *ots = arg_temp(op->args[idx]);
    TCGOpcode mov_opc = type_to_mov_opc(ots->type);

    tcg_debug_assert(!temp_readonly(ots));

    /* The only permitted operation to define a PHI directly is STORE of
     * TEMP_NORMAL, which should have been handled in tcg_opt_gen_mov().  */
    tcg_debug_assert(op->opc != mov_opc ||
                     /* MOVop reaches here must be CAST operation.  */
                     ots->type != arg_temp(op->args[1])->type);

    if (!ts_is_canonical(ots) && !temp_phi(ots)) {
        init_ts_info(ots, op);
    } else {
        TCGTemp *ts = tcg_opt_temp_new(ots->type);

        /* Updating PHI or CANONICAL VARIABLE using the result of
         * the operation, which can't be done without indirection.  */
        op->args[idx] = temp_arg(ts);
        init_ts_info(ts, op);
        if (temp_phi(ots)) {
            op = tcg_op_insert_after(tcg_ctx, op, mov_opc);
            op->args[0] = temp_arg(ots);
            op->args[1] = temp_arg(ts);
        } else {
            /* CANONICAL VARIABLEs are never modified, redefining
             * takes effect only through copy propagation.  */
        }
        ts_set_indirection(ots, ts);
    }
}

static bool init_its_info(TCGOp *op, size_t i)
{
    TCGTemp *its = arg_temp(op->args[i]);

    if (ts_is_initialized(its)) {
        return false;
    }
    switch (its->kind) {
    case TEMP_LOCAL:
    case TEMP_GLOBAL:
    {
        /* Direct use of PHI is unwanted as their updation may be unavoidable,
         * hence can't be used as SSA variable. So, add indirection by LOADing
         * from it, then use the resulted TEMP_NORMAL as CANONICAL VARIABLE.  */
        TCGOpcode mov_opc = type_to_mov_opc(its->type);
        TCGTemp *ts;
        bool done_this_op;

        if (op->opc == mov_opc && !temp_phi((ts = arg_temp(op->args[0])))) {
            /* The only operation permitted to use PHI directly is LOAD to
             * TEMP_NORMAL, i.e. the operation itself serves as indirection.  */
            done_this_op = true;

            if (!ts_is_canonical(ts)) {
                init_ts_info(ts, op);
            } else {
                TCGTemp *ts2 = tcg_opt_temp_new(ts->type);

                op->args[0] = temp_arg(ts2);
                init_ts_info(ts2, op);
                ts_set_indirection(ts, ts2);
            }
        } else {
            /* Otherwise, LOAD must be added as indirection. Note that, for
             * situation like `mov_opc %phi, %phi2` we only transform it to
             * `mov_opc %phi, %tmp` and leave it to tcg_opt_gen_mov().  */
            done_this_op = false;

            ts = tcg_opt_temp_new(its->type);
            op = tcg_op_insert_before(tcg_ctx, op, mov_opc);
            op->args[0] = temp_arg(ts);
            op->args[1] = temp_arg(its);
            init_ts_info(ts, op);
        }
        /* Do the opposite of tcg_opt_gen_mov() by setting the INDIRECTION of
         * SRC_TS to DST_TS. Use ts_indirection() to merge code path where TS
         * is not the right CANONICAL VARIABLE.  */
        ts_set_indirection(its, ts_indirection(ts));
        return done_this_op;
    }
    case TEMP_FIXED:
    case TEMP_CONST:
        init_ts_info(its, NULL);
        return false;
    default:
        /* TEMP_NORMAL temporaries must be initialized before use.  */
        g_assert_not_reached();
    }
}

static bool tcg_opt_gen_mov__unchecked(TCGOp *op, TCGArg dst, TCGArg src)
{
    TCGTemp *dst_ts = arg_temp(dst);
    TCGTemp *src_ts = arg_temp(src);
    const TCGOpDef *def = &tcg_op_defs[op->opc];
    TCGOpcode opc;

    tcg_debug_assert(!temp_readonly(dst_ts));

    /* Moving to DST_TS can be suppressed if its INDIRECTION is already
     * set to SRC_TS. Removing this OP will not affect:
     * 1. the outcome of compile time copy propagation, which only
     *    examines INDIRECTION, or
     * 2. the runtime value of PHI, otherwise its INDIRECTION would
     *    not have been set to SRC_TS.  */
    if (ts_is_initialized(dst_ts) && ts_indirection(dst_ts) == src_ts) {
        tcg_op_remove(tcg_ctx, op);
        return true;
    }

    if (def->flags & TCG_OPF_VECTOR) {
        opc = INDEX_op_mov_vec;
    } else if (def->flags & TCG_OPF_64BIT) {
        opc = INDEX_op_mov_i64;
    } else {
        opc = INDEX_op_mov_i32;
    }
    /* Size of opcode should follow that of the OARG.  */
    tcg_debug_assert(opc == type_to_mov_opc(dst_ts->type));

    op->opc = opc;
    /* TCGOP_VECL and TCGOP_VECE remain unchanged.  */
    op->args[0] = dst;
    op->args[1] = src;

    if (dst_ts->type == src_ts->type) {
        /* Moving between the same type only serves as a propagation of
         * INDIRECTION, except for PHIs, of which modifications must be
         * preserved. For TEMP_NORMALs, MOVop takes effect only through
         * copy propagation.  */
        if (!temp_phi(dst_ts)) {
            tcg_op_remove(tcg_ctx, op);
        }
        ts_set_indirection(dst_ts, src_ts);
        return true;
    } else {
        /* Moving between different types is interpreted as a cast
         * operation and may involve further data manipulation.  */
        return false;
    }
}

static void tcg_opt_gen_mov(TCGOp *op, TCGArg dst, TCGArg src)
{
    tcg_debug_assert(tcg_opt_gen_mov__unchecked(op, dst, src));
}

static void tcg_opt_gen_movi(TCGOp *op, TCGArg dst, uint64_t value)
{
    const TCGOpDef *def = &tcg_op_defs[op->opc];
    TCGType type;

    if (def->flags & TCG_OPF_VECTOR) {
        type = TCGOP_VECL(op) + TCG_TYPE_V64;
    } else if (def->flags & TCG_OPF_64BIT) {
        type = TCG_TYPE_I64;
    } else {
        type = TCG_TYPE_I32;
    }
    tcg_opt_gen_mov(op, dst, tcg_opt_constant_new(type, value));
}

/* Wrapper functions for arguments with type TCGArg.  */
static bool arg_is_const(TCGArg arg)
{
    return ts_is_const(arg_temp(arg));
}

static uint64_t arg_value(TCGArg arg)
{
    return ts_value(arg_temp(arg));
}

static TempOptInfo *arg_info(TCGArg arg)
{
    return ts_info(arg_temp(arg));
}

/* With tcg_optimize() now enforcing SSA-form of IR, IARGs are now copy
 * propagated to THE sole CANONICAL VARIABLE before peepholes, as such,
 * direct comparison suffices to test copies.  */
static bool args_are_copies(TCGArg iarg1, TCGArg iarg2)
{
    return iarg1 == iarg2;
}

static void tcg_opt_aggregate_offset(TCGOp *op)
{
    TCGOp *def_op = temp_definition(arg_temp(op->args[1]));
    int64_t offset;

    switch (op->opc) {
    CASE_OP_32_64(add):
        offset = arg_value(op->args[2]);
        break;
    case INDEX_op_sub_i32:
        op->opc = INDEX_op_add_i32;
        /* subi<i32>(constant<i32>) <=> addi<i32>(neg<i32>(constant<i32>))
         * holds for all constant<i32> /in [-2**31, 2**31).  */
        offset = -((int32_t) arg_value(op->args[2]));
        break;
    case INDEX_op_sub_i64:
        op->opc = INDEX_op_add_i64;
        offset = -arg_value(op->args[2]);
        break;
    default:
        g_assert_not_reached();
    }

    if (def_op) {
        switch (def_op->opc) {
        CASE_OP_32_64(add):
            if (arg_is_const(def_op->args[2])) {
                offset += arg_value(def_op->args[2]);
                op->args[1] = def_op->args[1];
            }
            if (def_op->opc == INDEX_op_add_i32
                && unlikely(offset != (int32_t) offset)) {
                offset = (int32_t) offset;
            }
            break;
        CASE_OP_32_64(sub):
            /* Previous SUBI operations should have been transformed
             * into ADDIs.  */
            tcg_debug_assert(!arg_is_const(def_op->args[2]));
            break;
        default:
            break;
        }
    }
    op->args[2] = tcg_opt_constant_new(arg_temp(op->args[2])->type, offset);
}

static TCGOp *tcg_opt_gen_tlb_load(TCGOp *op, TCGTemp *addr, uint32_t mmu_idx)
{
    TCGTemp *entry = tcg_opt_temp_new(TCG_TYPE_PTR);

    /* TLB_LOAD operates on TCG_TYPE_TL IARG directly.  */
    tcg_debug_assert(addr->type == TCG_TYPE_TL);

    /* Calculate page number and scale by factor of sizeof(CPUTLBEntry); Load
     * mask and TLB base address from env_cpu implicitly; Mask page number to
     * get TLB index, and eventually the TLB entry. Packed as one TCGOp.  */
    op = tcg_op_insert_after(tcg_ctx, op, INDEX_op_tlb_load);
    op->args[0] = temp_arg(entry);
    op->args[1] = temp_arg(addr);
    op->args[2] = mmu_idx;
    return op;
}

static TCGOp *tcg_opt_gen_extract_comparator(TCGOp *op, TCGTemp *addr,
                                             MemOp memop)
{
    uint32_t a_bits = get_alignment_bits(memop);
    uint32_t s_bits = memop & MO_SIZE;
    uint32_t a_mask = (1 << a_bits) - 1;
    uint32_t s_mask = (1 << s_bits) - 1;
    TCGTemp *comparator_ = tcg_opt_temp_new(TCG_TYPE_TL);

    if (a_bits >= s_bits) {
        /* Alignment check implies the cross-page check for accesses with
         * natural (or more strict) alignment restrictions.  */
    } else {
        TCGTemp *padded_addr = tcg_opt_temp_new(TCG_TYPE_TL);

        /* Otherwise, we pad the address to the last byte of the access WITH
         * THE ASSUMPTION THAT THE ADDRESS ITSELF IS ALIGNED, so that further
         * comparison fails if EITHER of the requirement is not met.  */
        op = tcg_op_insert_after(tcg_ctx, op, INDEX_op_add_tl);
        op->args[0] = temp_arg(padded_addr);
        op->args[1] = temp_arg(addr);
        op->args[2] = tcg_opt_constant_new(TCG_TYPE_TL, s_mask - a_mask);
        addr = padded_addr;
    }

    op = tcg_op_insert_after(tcg_ctx, op, INDEX_op_and_tl);
    op->args[0] = temp_arg(comparator_);
    op->args[1] = temp_arg(addr);
    op->args[2] = tcg_opt_constant_new(TCG_TYPE_TL, TARGET_PAGE_MASK | a_mask);
    return op;
}

static TCGOp *tcg_opt_gen_tlb_check(TCGOp *op, TCGTemp *entry, TCGTemp *addr,
                                    TCGMemOpIdx oi, bool is_load)
{
    op = tcg_op_insert_after(tcg_ctx, op, INDEX_op_tlb_check);
    op->args[0] = temp_arg(entry);
    /* comparator_ */
    op->args[1] = QTAILQ_PREV(op, link)->args[0];
    op->args[2] = temp_arg(addr);
    op->args[3] = oi | (is_load ? _OI_LOAD : 0);
    return op;
}

static TCGOp *tcg_opt_gen_gva_addend(TCGOp *op, TCGTemp *entry, TCGTemp *addr)
{
    TCGTemp *addend = tcg_opt_temp_new(TCG_TYPE_PTR);
    TCGTemp *hva = tcg_opt_temp_new(TCG_TYPE_PTR);

    _Static_assert(TCG_TARGET_REG_BITS == 64);

    op = tcg_op_insert_after(tcg_ctx, op, INDEX_op_ld_i64);
    op->args[0] = temp_arg(addend);
    op->args[1] = temp_arg(entry);
    op->args[2] = offsetof(CPUTLBEntry, addend);

    /* Zero extend 32-bit guest address, if necessary. TCG conservatively
     * assumes high bits always contain garbage regardless of the backend,
     * we follow this tradition.  */
    if (TCG_TYPE_TL != TCG_TYPE_PTR) {
        TCGTemp *_addr = tcg_opt_temp_new(TCG_TYPE_PTR);

        op = tcg_op_insert_after(tcg_ctx, op, INDEX_op_extu_i32_i64);
        op->args[0] = temp_arg(_addr);
        op->args[1] = temp_arg(addr);
        addr = _addr;
    }
    tcg_debug_assert(addr->type == TCG_TYPE_I64);

    op = tcg_op_insert_after(tcg_ctx, op, INDEX_op_add_i64);
    op->args[0] = temp_arg(hva);
    op->args[1] = temp_arg(addr);
    op->args[2] = temp_arg(addend);
    return op;
}

static TCGOpcode memop_to_ldst_opc(MemOp memop, bool is_load, bool is_64bit)
{
    static const TCGOpcode ldst_opc[2][2][8] = {
        {
            {
                [MO_UB] = INDEX_op_st8_i32,
                [MO_UW] = INDEX_op_st16_i32,
                [MO_UL] = INDEX_op_st_i32,
            },
            {
                [MO_UB] = INDEX_op_st8_i64,
                [MO_UW] = INDEX_op_st16_i64,
                [MO_UL] = INDEX_op_st32_i64,
                [MO_Q]  = INDEX_op_st_i64,
            },
        },
        {
            {
                [MO_UB] = INDEX_op_ld8u_i32,
                [MO_SB] = INDEX_op_ld8s_i32,
                [MO_UW] = INDEX_op_ld16u_i32,
                [MO_SW] = INDEX_op_ld16s_i32,
                [MO_UL] = INDEX_op_ld_i32,
            },
            {
                [MO_UB] = INDEX_op_ld8u_i64,
                [MO_SB] = INDEX_op_ld8s_i64,
                [MO_UW] = INDEX_op_ld16u_i64,
                [MO_SW] = INDEX_op_ld16s_i64,
                [MO_UL] = INDEX_op_ld32u_i64,
                [MO_SL] = INDEX_op_ld32s_i64,
                [MO_Q]  = INDEX_op_ld_i64,
            },
        },
    };

#ifdef CONFIG_DEBUG_TCG
    switch (memop & MO_SSIZE) {
    case MO_Q:
        tcg_debug_assert(is_64bit);
    case MO_UL:
    case MO_UW:
    case MO_UB:
        break;
    case MO_SL:
        tcg_debug_assert(is_64bit);
    case MO_SW:
    case MO_SB:
        tcg_debug_assert(is_load);
        break;
    default:
        g_assert_not_reached();
    }
#endif

    return ldst_opc[is_load][is_64bit][memop & MO_SSIZE];
}

static TCGOp *tcg_opt_gen_ldst(TCGOp *op, TCGTemp *value, TCGTemp *base,
                               intptr_t offset, MemOp memop, bool is_load,
                               bool is_64bit)
{
    TCGOpcode opc = memop_to_ldst_opc(memop, is_load, is_64bit);

    /* OFFSET to an associated base address is bounded by the speculation
     * threshold and should always be able to be encoded into instructions,
     * at least for x86_64 host.  */
    tcg_debug_assert(offset == (int32_t) offset);

    op = tcg_op_insert_after(tcg_ctx, op, opc);
    /* A LOAD here may violate SSA property of the IR sequence, but will
     * be fixed by further transformation.  */
    op->args[0] = temp_arg(value);
    op->args[1] = temp_arg(base);
    op->args[2] = offset;
    return op;
}

static void tcg_opt_qemu_ldst_finalize(TCGOp *op, bool is_load, bool is_64bit)
{
    TCGTemp *value = arg_temp(op->args[0]);
    TCGTemp *addr = arg_temp(op->args[1]);
    TCGMemOpIdx oi = op->args[2];
    uint32_t mmu_idx = get_mmuidx(oi);
    MemOp memop = get_memop(oi);
    TCGTemp *entry, *hva;

    /* Host should be 64-bit, with 64-bit pointer types.  */
    tcg_debug_assert(TCG_TYPE_PTR == TCG_TYPE_I64);

    /* Old qemu_{ld, st} is about to be separated into side-effect-less
     * opcodes, but there still needs to be a TCGOp which serves as the
     * carrier for the overall TCG_OPF_SIDE_EFFECTS for memory accesses.  */
    op->opc = INDEX_op_side_effect;

    /* Calculate TLB entry for address ADDR.  */
    op = tcg_opt_gen_tlb_load(op, addr, mmu_idx);
    entry = arg_temp(op->args[0]);

    /* Extract TLB comparator from ADDR, and check to see if:
     * 1. this is the address cached in TLB, and
     * 2. this is an aligned, within-page, ordinary RAM access.
     * Not satisfying the first condition causes an MMU walk and bails out
     * only if MMU exception is encountered, otherwise, execution returns
     * with TLB entry refilled.
     * Execution never returns on violation of the second condition.  */
    op = tcg_opt_gen_extract_comparator(op, addr, memop);
    op = tcg_opt_gen_tlb_check(op, entry, addr, oi, is_load);

    /* TLB hit, load ADDEND from TLB entry and calculate the host address
     * corresponding to the guest access.  */
    op = tcg_opt_gen_gva_addend(op, entry, addr);
    hva = arg_temp(op->args[0]);

    /* Perform the actual memory access.  */
    tcg_opt_gen_ldst(op, value, hva, 0, memop, is_load, is_64bit);
}

static uint64_t do_constant_folding_2(TCGOpcode op, uint64_t x, uint64_t y)
{
    uint64_t l64, h64;

    switch (op) {
    CASE_OP_32_64(add):
        return x + y;

    CASE_OP_32_64(sub):
        return x - y;

    CASE_OP_32_64(mul):
        return x * y;

    CASE_OP_32_64(and):
        return x & y;

    CASE_OP_32_64(or):
        return x | y;

    CASE_OP_32_64(xor):
        return x ^ y;

    case INDEX_op_shl_i32:
        return (uint32_t)x << (y & 31);

    case INDEX_op_shl_i64:
        return (uint64_t)x << (y & 63);

    case INDEX_op_shr_i32:
        return (uint32_t)x >> (y & 31);

    case INDEX_op_shr_i64:
        return (uint64_t)x >> (y & 63);

    case INDEX_op_sar_i32:
        return (int32_t)x >> (y & 31);

    case INDEX_op_sar_i64:
        return (int64_t)x >> (y & 63);

    case INDEX_op_rotr_i32:
        return ror32(x, y & 31);

    case INDEX_op_rotr_i64:
        return ror64(x, y & 63);

    case INDEX_op_rotl_i32:
        return rol32(x, y & 31);

    case INDEX_op_rotl_i64:
        return rol64(x, y & 63);

    CASE_OP_32_64(not):
        return ~x;

    CASE_OP_32_64(neg):
        return -x;

    CASE_OP_32_64(andc):
        return x & ~y;

    CASE_OP_32_64(orc):
        return x | ~y;

    CASE_OP_32_64(eqv):
        return ~(x ^ y);

    CASE_OP_32_64(nand):
        return ~(x & y);

    CASE_OP_32_64(nor):
        return ~(x | y);

    case INDEX_op_clz_i32:
        return (uint32_t)x ? clz32(x) : y;

    case INDEX_op_clz_i64:
        return x ? clz64(x) : y;

    case INDEX_op_ctz_i32:
        return (uint32_t)x ? ctz32(x) : y;

    case INDEX_op_ctz_i64:
        return x ? ctz64(x) : y;

    case INDEX_op_ctpop_i32:
        return ctpop32(x);

    case INDEX_op_ctpop_i64:
        return ctpop64(x);

    CASE_OP_32_64(ext8s):
        return (int8_t)x;

    CASE_OP_32_64(ext16s):
        return (int16_t)x;

    CASE_OP_32_64(ext8u):
        return (uint8_t)x;

    CASE_OP_32_64(ext16u):
        return (uint16_t)x;

    CASE_OP_32_64(bswap16):
        return bswap16(x);

    CASE_OP_32_64(bswap32):
        return bswap32(x);

    case INDEX_op_bswap64_i64:
        return bswap64(x);

    case INDEX_op_ext_i32_i64:
    case INDEX_op_ext32s_i64:
        return (int32_t)x;

    case INDEX_op_extu_i32_i64:
    case INDEX_op_extrl_i64_i32:
    case INDEX_op_ext32u_i64:
        return (uint32_t)x;

    case INDEX_op_extrh_i64_i32:
        return (uint64_t)x >> 32;

    case INDEX_op_muluh_i32:
        return ((uint64_t)(uint32_t)x * (uint32_t)y) >> 32;
    case INDEX_op_mulsh_i32:
        return ((int64_t)(int32_t)x * (int32_t)y) >> 32;

    case INDEX_op_muluh_i64:
        mulu64(&l64, &h64, x, y);
        return h64;
    case INDEX_op_mulsh_i64:
        muls64(&l64, &h64, x, y);
        return h64;

    case INDEX_op_div_i32:
        /* Avoid crashing on divide by zero, otherwise undefined.  */
        return (int32_t)x / ((int32_t)y ? : 1);
    case INDEX_op_divu_i32:
        return (uint32_t)x / ((uint32_t)y ? : 1);
    case INDEX_op_div_i64:
        return (int64_t)x / ((int64_t)y ? : 1);
    case INDEX_op_divu_i64:
        return (uint64_t)x / ((uint64_t)y ? : 1);

    case INDEX_op_rem_i32:
        return (int32_t)x % ((int32_t)y ? : 1);
    case INDEX_op_remu_i32:
        return (uint32_t)x % ((uint32_t)y ? : 1);
    case INDEX_op_rem_i64:
        return (int64_t)x % ((int64_t)y ? : 1);
    case INDEX_op_remu_i64:
        return (uint64_t)x % ((uint64_t)y ? : 1);

    default:
        fprintf(stderr,
                "Unrecognized operation %d in do_constant_folding.\n", op);
        tcg_abort();
    }
}

static uint64_t do_constant_folding(TCGOpcode op, uint64_t x, uint64_t y)
{
    const TCGOpDef *def = &tcg_op_defs[op];
    uint64_t res = do_constant_folding_2(op, x, y);
    if (!(def->flags & TCG_OPF_64BIT)) {
        res = (int32_t)res;
    }
    return res;
}

static bool do_constant_folding_cond_32(uint32_t x, uint32_t y, TCGCond c)
{
    switch (c) {
    case TCG_COND_EQ:
        return x == y;
    case TCG_COND_NE:
        return x != y;
    case TCG_COND_LT:
        return (int32_t)x < (int32_t)y;
    case TCG_COND_GE:
        return (int32_t)x >= (int32_t)y;
    case TCG_COND_LE:
        return (int32_t)x <= (int32_t)y;
    case TCG_COND_GT:
        return (int32_t)x > (int32_t)y;
    case TCG_COND_LTU:
        return x < y;
    case TCG_COND_GEU:
        return x >= y;
    case TCG_COND_LEU:
        return x <= y;
    case TCG_COND_GTU:
        return x > y;
    default:
        tcg_abort();
    }
}

static bool do_constant_folding_cond_64(uint64_t x, uint64_t y, TCGCond c)
{
    switch (c) {
    case TCG_COND_EQ:
        return x == y;
    case TCG_COND_NE:
        return x != y;
    case TCG_COND_LT:
        return (int64_t)x < (int64_t)y;
    case TCG_COND_GE:
        return (int64_t)x >= (int64_t)y;
    case TCG_COND_LE:
        return (int64_t)x <= (int64_t)y;
    case TCG_COND_GT:
        return (int64_t)x > (int64_t)y;
    case TCG_COND_LTU:
        return x < y;
    case TCG_COND_GEU:
        return x >= y;
    case TCG_COND_LEU:
        return x <= y;
    case TCG_COND_GTU:
        return x > y;
    default:
        tcg_abort();
    }
}

static bool do_constant_folding_cond_eq(TCGCond c)
{
    switch (c) {
    case TCG_COND_GT:
    case TCG_COND_LTU:
    case TCG_COND_LT:
    case TCG_COND_GTU:
    case TCG_COND_NE:
        return 0;
    case TCG_COND_GE:
    case TCG_COND_GEU:
    case TCG_COND_LE:
    case TCG_COND_LEU:
    case TCG_COND_EQ:
        return 1;
    default:
        tcg_abort();
    }
}

/* Return 2 if the condition can't be simplified, and the result
   of the condition (0 or 1) if it can */
static TCGArg do_constant_folding_cond(TCGOpcode op, TCGArg x,
                                       TCGArg y, TCGCond c)
{
    if (arg_is_const(x) && arg_is_const(y)) {
        const TCGOpDef *def = &tcg_op_defs[op];
        uint64_t xv = arg_value(x);
        uint64_t yv = arg_value(y);

        tcg_debug_assert(!(def->flags & TCG_OPF_VECTOR));
        if (def->flags & TCG_OPF_64BIT) {
            return do_constant_folding_cond_64(xv, yv, c);
        } else {
            return do_constant_folding_cond_32(xv, yv, c);
        }
    } else if (args_are_copies(x, y)) {
        return do_constant_folding_cond_eq(c);
    } else if (arg_is_const(y) && arg_value(y) == 0) {
        switch (c) {
        case TCG_COND_LTU:
            return 0;
        case TCG_COND_GEU:
            return 1;
        default:
            return 2;
        }
    }
    return 2;
}

/* Return 2 if the condition can't be simplified, and the result
   of the condition (0 or 1) if it can */
static TCGArg do_constant_folding_cond2(TCGArg *p1, TCGArg *p2, TCGCond c)
{
    TCGArg al = p1[0], ah = p1[1];
    TCGArg bl = p2[0], bh = p2[1];

    if (arg_is_const(bl) && arg_is_const(bh)) {
        tcg_target_ulong blv = arg_value(bl);
        tcg_target_ulong bhv = arg_value(bh);
        uint64_t b = deposit64(blv, 32, 32, bhv);

        if (arg_is_const(al) && arg_is_const(ah)) {
            tcg_target_ulong alv = arg_value(al);
            tcg_target_ulong ahv = arg_value(ah);
            uint64_t a = deposit64(alv, 32, 32, ahv);
            return do_constant_folding_cond_64(a, b, c);
        }
        if (b == 0) {
            switch (c) {
            case TCG_COND_LTU:
                return 0;
            case TCG_COND_GEU:
                return 1;
            default:
                break;
            }
        }
    }
    if (args_are_copies(al, bl) && args_are_copies(ah, bh)) {
        return do_constant_folding_cond_eq(c);
    }
    return 2;
}

static bool swap_commutative(TCGArg dest, TCGArg *p1, TCGArg *p2)
{
    TCGArg a1 = *p1, a2 = *p2;
    int sum = 0;
    sum += arg_is_const(a1);
    sum -= arg_is_const(a2);

    /* Prefer the constant in second argument, and then the form
       op a, a, b, which is better handled on non-RISC hosts. */
    if (sum > 0 || (sum == 0 && dest == a2)) {
        *p1 = a2;
        *p2 = a1;
        return true;
    }
    return false;
}

static bool swap_commutative2(TCGArg *p1, TCGArg *p2)
{
    int sum = 0;
    sum += arg_is_const(p1[0]);
    sum += arg_is_const(p1[1]);
    sum -= arg_is_const(p2[0]);
    sum -= arg_is_const(p2[1]);
    if (sum > 0) {
        TCGArg t;
        t = p1[0], p1[0] = p2[0], p2[0] = t;
        t = p1[1], p1[1] = p2[1], p2[1] = t;
        return true;
    }
    return false;
}

static void tcg_opt_convert_to_ssa_and_peephole(TCGContext *s)
{
    TCGOp *op, *op_next, *prev_mb = NULL;
    size_t i;

    for (i = 0; i < s->nb_temps; i++) {
        ts_set_uninitialized(&s->temps[i]);
    }

    QTAILQ_FOREACH_SAFE(op, &s->ops, link, op_next) {
        uint64_t mask, partmask, affected, tmp;
        uint8_t nb_oargs, nb_iargs;
        TCGOpcode opc = op->opc;
        const TCGOpDef *def = &tcg_op_defs[opc];
        TCGTemp *ts;

        /* Count arguments, and initialize all input ones, this will catch
         * all variables that are read before written to.  */
        if (opc == INDEX_op_call) {
            nb_oargs = TCGOP_CALLO(op);
            nb_iargs = TCGOP_CALLI(op);
        } else {
            nb_oargs = def->nb_oargs;
            nb_iargs = def->nb_iargs;
        }
        for (i = nb_oargs; i < nb_oargs + nb_iargs; i++) {
            if (unlikely(op->args[i] == TCG_CALL_DUMMY_ARG)) {
                continue;
            }
            if (init_its_info(op, i)) {
                goto done_this_op;
            }
        }

        /* Decomposition and finalization of QEMU_{LD, ST} opcode, NOTE THAT
         * THIS MUST BE DONE BEFORE COPY PROPAGATION. Otherwise, the original
         * ADDR or VALUE temporary may be "dereference"d twice -- once in the
         * old QEMU_{LD, ST} opcode, and once in new opcodes generated below,
         * for example TLB_LOAD entry, *ADDR*, mmu_idx.  */
        if (!use_monolithic_ldst()) {
            bool is_load, is_64bit;

            switch (opc) {
            case INDEX_op_qemu_ld_i32:
                is_load = true, is_64bit = false;
                goto do_finalize;
            case INDEX_op_qemu_ld_i64:
                is_load = true, is_64bit = true;
                goto do_finalize;
            case INDEX_op_qemu_st_i32:
                is_load = false, is_64bit = false;
                goto do_finalize;
            case INDEX_op_qemu_st_i64:
                is_load = false, is_64bit = true;
            do_finalize:
                tcg_opt_qemu_ldst_finalize(op, is_load, is_64bit);
                op_next = QTAILQ_NEXT(op, link);
                continue;
            default:
                break;
            }
        }

        for (i = nb_oargs; i < nb_oargs + nb_iargs; i++) {
            if (unlikely(op->args[i] == TCG_CALL_DUMMY_ARG)) {
                continue;
            }
            /* Do copy propagation.  */
            op->args[i] = temp_arg(ts_indirection(arg_temp(op->args[i])));
        }

        /* For commutative operations make constant second argument */
        switch (opc) {
        CASE_OP_32_64_VEC(add):
        CASE_OP_32_64_VEC(mul):
        CASE_OP_32_64_VEC(and):
        CASE_OP_32_64_VEC(or):
        CASE_OP_32_64_VEC(xor):
        CASE_OP_32_64(eqv):
        CASE_OP_32_64(nand):
        CASE_OP_32_64(nor):
        CASE_OP_32_64(muluh):
        CASE_OP_32_64(mulsh):
            swap_commutative(op->args[0], &op->args[1], &op->args[2]);
            break;
        CASE_OP_32_64(brcond):
            if (swap_commutative(-1, &op->args[0], &op->args[1])) {
                op->args[2] = tcg_swap_cond(op->args[2]);
            }
            break;
        CASE_OP_32_64(setcond):
            if (swap_commutative(op->args[0], &op->args[1], &op->args[2])) {
                op->args[3] = tcg_swap_cond(op->args[3]);
            }
            break;
        CASE_OP_32_64(movcond):
            if (swap_commutative(-1, &op->args[1], &op->args[2])) {
                op->args[5] = tcg_swap_cond(op->args[5]);
            }
            /* For movcond, we canonicalize the "false" input reg to match
               the destination reg so that the tcg backend can implement
               a "move if true" operation.  */
            if (swap_commutative(op->args[0], &op->args[4], &op->args[3])) {
                op->args[5] = tcg_invert_cond(op->args[5]);
            }
            break;
        CASE_OP_32_64(add2):
            swap_commutative(op->args[0], &op->args[2], &op->args[4]);
            swap_commutative(op->args[1], &op->args[3], &op->args[5]);
            break;
        CASE_OP_32_64(mulu2):
        CASE_OP_32_64(muls2):
            swap_commutative(op->args[0], &op->args[2], &op->args[3]);
            break;
        case INDEX_op_brcond2_i32:
            if (swap_commutative2(&op->args[0], &op->args[2])) {
                op->args[4] = tcg_swap_cond(op->args[4]);
            }
            break;
        case INDEX_op_setcond2_i32:
            if (swap_commutative2(&op->args[1], &op->args[3])) {
                op->args[5] = tcg_swap_cond(op->args[5]);
            }
            break;
        default:
            break;
        }

        /* Simplify expressions for "shift/rot r, 0, a => movi r, 0",
           and "sub r, 0, a => neg r, a" case.  */
        switch (opc) {
        CASE_OP_32_64(shl):
        CASE_OP_32_64(shr):
        CASE_OP_32_64(sar):
        CASE_OP_32_64(rotl):
        CASE_OP_32_64(rotr):
            if (arg_is_const(op->args[1])
                && arg_value(op->args[1]) == 0) {
                tcg_opt_gen_movi(op, op->args[0], 0);
                continue;
            }
            break;
        CASE_OP_32_64_VEC(sub):
            {
                TCGOpcode neg_op;
                bool have_neg;

                if (arg_is_const(op->args[2])) {
                    /* Proceed with possible constant folding. */
                    break;
                }
                if (opc == INDEX_op_sub_i32) {
                    neg_op = INDEX_op_neg_i32;
                    have_neg = TCG_TARGET_HAS_neg_i32;
                } else if (opc == INDEX_op_sub_i64) {
                    neg_op = INDEX_op_neg_i64;
                    have_neg = TCG_TARGET_HAS_neg_i64;
                } else if (TCG_TARGET_HAS_neg_vec) {
                    TCGType type = TCGOP_VECL(op) + TCG_TYPE_V64;
                    unsigned vece = TCGOP_VECE(op);
                    neg_op = INDEX_op_neg_vec;
                    have_neg = tcg_can_emit_vec_op(neg_op, type, vece) > 0;
                } else {
                    break;
                }
                if (!have_neg) {
                    break;
                }
                if (arg_is_const(op->args[1])
                    && arg_value(op->args[1]) == 0) {
                    opc = op->opc = neg_op;
                    op->args[1] = op->args[2];
                    goto done_algebraic_simplifying_and_constant_folding;
                }
            }
            break;
        CASE_OP_32_64_VEC(xor):
        CASE_OP_32_64(nand):
            if (!arg_is_const(op->args[1])
                && arg_is_const(op->args[2])
                && arg_value(op->args[2]) == -1) {
                i = 1;
                goto try_not;
            }
            break;
        CASE_OP_32_64(nor):
            if (!arg_is_const(op->args[1])
                && arg_is_const(op->args[2])
                && arg_value(op->args[2]) == 0) {
                i = 1;
                goto try_not;
            }
            break;
        CASE_OP_32_64_VEC(andc):
            if (!arg_is_const(op->args[2])
                && arg_is_const(op->args[1])
                && arg_value(op->args[1]) == -1) {
                i = 2;
                goto try_not;
            }
            break;
        CASE_OP_32_64_VEC(orc):
        CASE_OP_32_64(eqv):
            if (!arg_is_const(op->args[2])
                && arg_is_const(op->args[1])
                && arg_value(op->args[1]) == 0) {
                i = 2;
                goto try_not;
            }
            break;
        try_not:
            {
                TCGOpcode not_op;
                bool have_not;

                if (def->flags & TCG_OPF_VECTOR) {
                    not_op = INDEX_op_not_vec;
                    have_not = TCG_TARGET_HAS_not_vec;
                } else if (def->flags & TCG_OPF_64BIT) {
                    not_op = INDEX_op_not_i64;
                    have_not = TCG_TARGET_HAS_not_i64;
                } else {
                    not_op = INDEX_op_not_i32;
                    have_not = TCG_TARGET_HAS_not_i32;
                }
                if (!have_not) {
                    break;
                }
                opc = op->opc = not_op;
                op->args[1] = op->args[i];
                goto done_algebraic_simplifying_and_constant_folding;
            }
        default:
            break;
        }

        /* Simplify expression for "op r, a, const => mov r, a" cases */
        switch (opc) {
        CASE_OP_32_64_VEC(add):
        CASE_OP_32_64_VEC(sub):
        CASE_OP_32_64_VEC(or):
        CASE_OP_32_64_VEC(xor):
        CASE_OP_32_64_VEC(andc):
        CASE_OP_32_64(shl):
        CASE_OP_32_64(shr):
        CASE_OP_32_64(sar):
        CASE_OP_32_64(rotl):
        CASE_OP_32_64(rotr):
            if (!arg_is_const(op->args[1])
                && arg_is_const(op->args[2])
                && arg_value(op->args[2]) == 0) {
                tcg_opt_gen_mov(op, op->args[0], op->args[1]);
                continue;
            }
            break;
        CASE_OP_32_64_VEC(and):
        CASE_OP_32_64_VEC(orc):
        CASE_OP_32_64(eqv):
            if (!arg_is_const(op->args[1])
                && arg_is_const(op->args[2])
                && arg_value(op->args[2]) == -1) {
                tcg_opt_gen_mov(op, op->args[0], op->args[1]);
                continue;
            }
            break;
        default:
            break;
        }

        /* Simplify expression for "op r, a, 0 => movi r, 0" cases */
        switch (opc) {
        CASE_OP_32_64_VEC(and):
        CASE_OP_32_64_VEC(mul):
        CASE_OP_32_64(muluh):
        CASE_OP_32_64(mulsh):
            if (arg_is_const(op->args[2])
                && arg_value(op->args[2]) == 0) {
                tcg_opt_gen_movi(op, op->args[0], 0);
                continue;
            }
            break;
        default:
            break;
        }

        /* Simplify expression for "op r, a, a => mov r, a" cases */
        switch (opc) {
        CASE_OP_32_64_VEC(or):
        CASE_OP_32_64_VEC(and):
            if (args_are_copies(op->args[1], op->args[2])) {
                tcg_opt_gen_mov(op, op->args[0], op->args[1]);
                continue;
            }
            break;
        default:
            break;
        }

        /* Simplify expression for "op r, a, a => movi r, 0" cases */
        switch (opc) {
        CASE_OP_32_64_VEC(andc):
        CASE_OP_32_64_VEC(sub):
        CASE_OP_32_64_VEC(xor):
            if (args_are_copies(op->args[1], op->args[2])) {
                tcg_opt_gen_movi(op, op->args[0], 0);
                continue;
            }
            break;
        default:
            break;
        }

        /* Propagate constants through copy operations and do constant
         * folding.  Constants will be substituted to arguments by register
         * allocator where needed and possible. Also detect copies.  */
        switch (opc) {
        CASE_OP_32_64_VEC(mov):
            if (tcg_opt_gen_mov__unchecked(op, op->args[0], op->args[1])) {
                continue;
            }
            break;

        case INDEX_op_dup_vec:
            if (arg_is_const(op->args[1])) {
                tmp = arg_value(op->args[1]);
                tmp = dup_const(TCGOP_VECE(op), tmp);
                tcg_opt_gen_movi(op, op->args[0], tmp);
                continue;
            }
            break;

        case INDEX_op_dup2_vec:
            assert(TCG_TARGET_REG_BITS == 32);
            if (arg_is_const(op->args[1]) && arg_is_const(op->args[2])) {
                tcg_opt_gen_movi(op, op->args[0],
                                 deposit64(arg_value(op->args[1]), 32, 32,
                                           arg_value(op->args[2])));
                continue;
            } else if (args_are_copies(op->args[1], op->args[2])) {
                opc = op->opc = INDEX_op_dup_vec;
                TCGOP_VECE(op) = MO_32;
            }
            break;

        CASE_OP_32_64(not):
        CASE_OP_32_64(neg):
        CASE_OP_32_64(ext8s):
        CASE_OP_32_64(ext8u):
        CASE_OP_32_64(ext16s):
        CASE_OP_32_64(ext16u):
        CASE_OP_32_64(ctpop):
        CASE_OP_32_64(bswap16):
        CASE_OP_32_64(bswap32):
        case INDEX_op_bswap64_i64:
        case INDEX_op_ext32s_i64:
        case INDEX_op_ext32u_i64:
        case INDEX_op_ext_i32_i64:
        case INDEX_op_extu_i32_i64:
        case INDEX_op_extrl_i64_i32:
        case INDEX_op_extrh_i64_i32:
            if (arg_is_const(op->args[1])) {
                tmp = do_constant_folding(opc, arg_value(op->args[1]), 0);
                tcg_opt_gen_movi(op, op->args[0], tmp);
                continue;
            }
            break;

        CASE_OP_32_64(add):
        CASE_OP_32_64(sub):
            if (!arg_is_const(op->args[1]) && arg_is_const(op->args[2])) {
                tcg_opt_aggregate_offset(op);
                opc = op->opc;
                break;
            }
        CASE_OP_32_64(mul):
        CASE_OP_32_64(or):
        CASE_OP_32_64(and):
        CASE_OP_32_64(xor):
        CASE_OP_32_64(shl):
        CASE_OP_32_64(shr):
        CASE_OP_32_64(sar):
        CASE_OP_32_64(rotl):
        CASE_OP_32_64(rotr):
        CASE_OP_32_64(andc):
        CASE_OP_32_64(orc):
        CASE_OP_32_64(eqv):
        CASE_OP_32_64(nand):
        CASE_OP_32_64(nor):
        CASE_OP_32_64(muluh):
        CASE_OP_32_64(mulsh):
        CASE_OP_32_64(div):
        CASE_OP_32_64(divu):
        CASE_OP_32_64(rem):
        CASE_OP_32_64(remu):
            if (arg_is_const(op->args[1]) && arg_is_const(op->args[2])) {
                tmp = do_constant_folding(opc, arg_value(op->args[1]),
                                          arg_value(op->args[2]));
                tcg_opt_gen_movi(op, op->args[0], tmp);
                continue;
            }
            break;

        CASE_OP_32_64(clz):
        CASE_OP_32_64(ctz):
            if (arg_is_const(op->args[1])) {
                TCGArg v = arg_value(op->args[1]);
                if (v != 0) {
                    tmp = do_constant_folding(opc, v, 0);
                    tcg_opt_gen_movi(op, op->args[0], tmp);
                } else {
                    tcg_opt_gen_mov(op, op->args[0], op->args[2]);
                }
                continue;
            }
            break;

        CASE_OP_32_64(deposit):
            if (arg_is_const(op->args[1]) && arg_is_const(op->args[2])) {
                tmp = deposit64(arg_value(op->args[1]),
                                op->args[3], op->args[4],
                                arg_value(op->args[2]));
                tcg_opt_gen_movi(op, op->args[0], tmp);
                continue;
            }
            break;

        CASE_OP_32_64(extract):
            if (arg_is_const(op->args[1])) {
                tmp = extract64(arg_value(op->args[1]),
                                op->args[2], op->args[3]);
                tcg_opt_gen_movi(op, op->args[0], tmp);
                continue;
            }
            break;

        CASE_OP_32_64(sextract):
            if (arg_is_const(op->args[1])) {
                tmp = sextract64(arg_value(op->args[1]),
                                 op->args[2], op->args[3]);
                tcg_opt_gen_movi(op, op->args[0], tmp);
                continue;
            }
            break;

        CASE_OP_32_64(extract2):
            if (arg_is_const(op->args[1]) && arg_is_const(op->args[2])) {
                uint64_t v1 = arg_value(op->args[1]);
                uint64_t v2 = arg_value(op->args[2]);
                int shr = op->args[3];

                if (opc == INDEX_op_extract2_i64) {
                    tmp = (v1 >> shr) | (v2 << (64 - shr));
                } else {
                    tmp = (int32_t)(((uint32_t)v1 >> shr) |
                                    ((uint32_t)v2 << (32 - shr)));
                }
                tcg_opt_gen_movi(op, op->args[0], tmp);
                continue;
            }
            break;

        CASE_OP_32_64(setcond):
            tmp = do_constant_folding_cond(opc, op->args[1],
                                           op->args[2], op->args[3]);
            if (tmp != 2) {
                tcg_opt_gen_movi(op, op->args[0], tmp);
                continue;
            }
            break;

        CASE_OP_32_64(brcond):
            tmp = do_constant_folding_cond(opc, op->args[0],
                                           op->args[1], op->args[2]);
            if (tmp != 2) {
                if (!tmp) {
                    tcg_op_remove(s, op);
                    continue;
                }
                opc = op->opc = INDEX_op_br;
                op->args[0] = op->args[3];
            }
            break;

        CASE_OP_32_64(movcond):
            tmp = do_constant_folding_cond(opc, op->args[1],
                                           op->args[2], op->args[5]);
            if (tmp != 2) {
                tcg_opt_gen_mov(op, op->args[0], op->args[4-tmp]);
                continue;
            }
            if (arg_is_const(op->args[3]) && arg_is_const(op->args[4])) {
                uint64_t tv = arg_value(op->args[3]);
                uint64_t fv = arg_value(op->args[4]);
                TCGCond cond = op->args[5];

                if (fv == 1 && tv == 0) {
                    cond = tcg_invert_cond(cond);
                } else if (!(tv == 1 && fv == 0)) {
                    break;
                }
                op->args[3] = cond;
                opc = op->opc = (opc == INDEX_op_movcond_i32
                                      ? INDEX_op_setcond_i32
                                      : INDEX_op_setcond_i64);
            }
            break;

        case INDEX_op_add2_i32:
        case INDEX_op_sub2_i32:
            if (arg_is_const(op->args[2]) && arg_is_const(op->args[3])
                && arg_is_const(op->args[4]) && arg_is_const(op->args[5])) {
                uint32_t al = arg_value(op->args[2]);
                uint32_t ah = arg_value(op->args[3]);
                uint32_t bl = arg_value(op->args[4]);
                uint32_t bh = arg_value(op->args[5]);
                uint64_t a = ((uint64_t)ah << 32) | al;
                uint64_t b = ((uint64_t)bh << 32) | bl;
                TCGArg rl, rh;
                TCGOp *op2 = tcg_op_insert_before(s, op, INDEX_op_mov_i32);

                if (opc == INDEX_op_add2_i32) {
                    a += b;
                } else {
                    a -= b;
                }

                rl = op->args[0];
                rh = op->args[1];
                tcg_opt_gen_movi(op, rl, (int32_t)a);
                tcg_opt_gen_movi(op2, rh, (int32_t)(a >> 32));
                continue;
            }
            break;

        case INDEX_op_mulu2_i32:
            if (arg_is_const(op->args[2]) && arg_is_const(op->args[3])) {
                uint32_t a = arg_value(op->args[2]);
                uint32_t b = arg_value(op->args[3]);
                uint64_t r = (uint64_t)a * b;
                TCGArg rl, rh;
                TCGOp *op2 = tcg_op_insert_before(s, op, INDEX_op_mov_i32);

                rl = op->args[0];
                rh = op->args[1];
                tcg_opt_gen_movi(op, rl, (int32_t)r);
                tcg_opt_gen_movi(op2, rh, (int32_t)(r >> 32));
                continue;
            }
            break;

        case INDEX_op_brcond2_i32:
            tmp = do_constant_folding_cond2(&op->args[0], &op->args[2],
                                            op->args[4]);
            if (tmp != 2) {
                if (!tmp) {
            do_brcond_false:
                    tcg_op_remove(s, op);
                    continue;
                }
            do_brcond_true:
                opc = op->opc = INDEX_op_br;
                op->args[0] = op->args[5];
            } else if ((op->args[4] == TCG_COND_LT
                        || op->args[4] == TCG_COND_GE)
                       && arg_is_const(op->args[2])
                       && arg_value(op->args[2]) == 0
                       && arg_is_const(op->args[3])
                       && arg_value(op->args[3]) == 0) {
                /* Simplify LT/GE comparisons vs zero to a single compare
                   vs the high word of the input.  */
            do_brcond_high:
                opc = op->opc = INDEX_op_brcond_i32;
                op->args[0] = op->args[1];
                op->args[1] = op->args[3];
                op->args[2] = op->args[4];
                op->args[3] = op->args[5];
            } else if (op->args[4] == TCG_COND_EQ) {
                /* Simplify EQ comparisons where one of the pairs
                   can be simplified.  */
                tmp = do_constant_folding_cond(INDEX_op_brcond_i32,
                                               op->args[0], op->args[2],
                                               TCG_COND_EQ);
                if (tmp == 0) {
                    goto do_brcond_false;
                } else if (tmp == 1) {
                    goto do_brcond_high;
                }
                tmp = do_constant_folding_cond(INDEX_op_brcond_i32,
                                               op->args[1], op->args[3],
                                               TCG_COND_EQ);
                if (tmp == 0) {
                    goto do_brcond_false;
                } else if (tmp == 1) {
            do_brcond_low:
                    opc = op->opc = INDEX_op_brcond_i32;
                    op->args[1] = op->args[2];
                    op->args[2] = op->args[4];
                    op->args[3] = op->args[5];
                }
            } else if (op->args[4] == TCG_COND_NE) {
                /* Simplify NE comparisons where one of the pairs
                   can be simplified.  */
                tmp = do_constant_folding_cond(INDEX_op_brcond_i32,
                                               op->args[0], op->args[2],
                                               TCG_COND_NE);
                if (tmp == 0) {
                    goto do_brcond_high;
                } else if (tmp == 1) {
                    goto do_brcond_true;
                }
                tmp = do_constant_folding_cond(INDEX_op_brcond_i32,
                                               op->args[1], op->args[3],
                                               TCG_COND_NE);
                if (tmp == 0) {
                    goto do_brcond_low;
                } else if (tmp == 1) {
                    goto do_brcond_true;
                }
            }
            break;

        case INDEX_op_setcond2_i32:
            tmp = do_constant_folding_cond2(&op->args[1], &op->args[3],
                                            op->args[5]);
            if (tmp != 2) {
            do_setcond_const:
                tcg_opt_gen_movi(op, op->args[0], tmp);
                continue;
            } else if ((op->args[5] == TCG_COND_LT
                        || op->args[5] == TCG_COND_GE)
                       && arg_is_const(op->args[3])
                       && arg_value(op->args[3]) == 0
                       && arg_is_const(op->args[4])
                       && arg_value(op->args[4]) == 0) {
                /* Simplify LT/GE comparisons vs zero to a single compare
                   vs the high word of the input.  */
            do_setcond_high:
                opc = op->opc = INDEX_op_setcond_i32;
                op->args[1] = op->args[2];
                op->args[2] = op->args[4];
                op->args[3] = op->args[5];
            } else if (op->args[5] == TCG_COND_EQ) {
                /* Simplify EQ comparisons where one of the pairs
                   can be simplified.  */
                tmp = do_constant_folding_cond(INDEX_op_setcond_i32,
                                               op->args[1], op->args[3],
                                               TCG_COND_EQ);
                if (tmp == 0) {
                    goto do_setcond_const;
                } else if (tmp == 1) {
                    goto do_setcond_high;
                }
                tmp = do_constant_folding_cond(INDEX_op_setcond_i32,
                                               op->args[2], op->args[4],
                                               TCG_COND_EQ);
                if (tmp == 0) {
                    goto do_setcond_const;
                } else if (tmp == 1) {
            do_setcond_low:
                    opc = op->opc = INDEX_op_setcond_i32;
                    op->args[2] = op->args[3];
                    op->args[3] = op->args[5];
                }
            } else if (op->args[5] == TCG_COND_NE) {
                /* Simplify NE comparisons where one of the pairs
                   can be simplified.  */
                tmp = do_constant_folding_cond(INDEX_op_setcond_i32,
                                               op->args[1], op->args[3],
                                               TCG_COND_NE);
                if (tmp == 0) {
                    goto do_setcond_high;
                } else if (tmp == 1) {
                    goto do_setcond_const;
                }
                tmp = do_constant_folding_cond(INDEX_op_setcond_i32,
                                               op->args[2], op->args[4],
                                               TCG_COND_NE);
                if (tmp == 0) {
                    goto do_setcond_low;
                } else if (tmp == 1) {
                    goto do_setcond_const;
                }
            }
            break;
        default:
            /* Default case: we know nothing about operation (or were unable
             * to compute the operation result) so no propagation is done.  */
            break;
        }

done_algebraic_simplifying_and_constant_folding:
        /* Simplify using known-zero bits. Currently only ops with a single
           output argument is supported. */
        mask = -1;
        affected = -1;
        switch (opc) {
        CASE_OP_32_64(ext8s):
            if ((arg_info(op->args[1])->mask & 0x80) != 0) {
                break;
            }
        CASE_OP_32_64(ext8u):
            mask = 0xff;
            goto and_const;
        CASE_OP_32_64(ext16s):
            if ((arg_info(op->args[1])->mask & 0x8000) != 0) {
                break;
            }
        CASE_OP_32_64(ext16u):
            mask = 0xffff;
            goto and_const;
        case INDEX_op_ext32s_i64:
            if ((arg_info(op->args[1])->mask & 0x80000000) != 0) {
                break;
            }
        case INDEX_op_ext32u_i64:
            mask = 0xffffffffu;
            goto and_const;

        CASE_OP_32_64(and):
            mask = arg_info(op->args[2])->mask;
            if (arg_is_const(op->args[2])) {
        and_const:
                affected = arg_info(op->args[1])->mask & ~mask;
            }
            mask = arg_info(op->args[1])->mask & mask;
            break;

        case INDEX_op_ext_i32_i64:
            if ((arg_info(op->args[1])->mask & 0x80000000) != 0) {
                break;
            }
        case INDEX_op_extu_i32_i64:
            /* We do not compute affected as it is a size changing op.  */
            mask = (uint32_t)arg_info(op->args[1])->mask;
            break;

        CASE_OP_32_64(andc):
            /* Known-zeros does not imply known-ones.  Therefore unless
               op->args[2] is constant, we can't infer anything from it.  */
            if (arg_is_const(op->args[2])) {
                mask = ~arg_info(op->args[2])->mask;
                goto and_const;
            }
            /* But we certainly know nothing outside args[1] may be set. */
            mask = arg_info(op->args[1])->mask;
            break;

        case INDEX_op_sar_i32:
            if (arg_is_const(op->args[2])) {
                tmp = arg_value(op->args[2]) & 31;
                mask = (int32_t)arg_info(op->args[1])->mask >> tmp;
            }
            break;
        case INDEX_op_sar_i64:
            if (arg_is_const(op->args[2])) {
                tmp = arg_value(op->args[2]) & 63;
                mask = (int64_t)arg_info(op->args[1])->mask >> tmp;
            }
            break;

        case INDEX_op_shr_i32:
            if (arg_is_const(op->args[2])) {
                tmp = arg_value(op->args[2]) & 31;
                mask = (uint32_t)arg_info(op->args[1])->mask >> tmp;
            }
            break;
        case INDEX_op_shr_i64:
            if (arg_is_const(op->args[2])) {
                tmp = arg_value(op->args[2]) & 63;
                mask = (uint64_t)arg_info(op->args[1])->mask >> tmp;
            }
            break;

        case INDEX_op_extrl_i64_i32:
            mask = (uint32_t)arg_info(op->args[1])->mask;
            break;
        case INDEX_op_extrh_i64_i32:
            mask = (uint64_t)arg_info(op->args[1])->mask >> 32;
            break;

        CASE_OP_32_64(shl):
            if (arg_is_const(op->args[2])) {
                tmp = arg_value(op->args[2]) & (TCG_TARGET_REG_BITS - 1);
                mask = arg_info(op->args[1])->mask << tmp;
            }
            break;

        CASE_OP_32_64(neg):
            /* Set to 1 all bits to the left of the rightmost.  */
            mask = -(arg_info(op->args[1])->mask
                     & -arg_info(op->args[1])->mask);
            break;

        CASE_OP_32_64(deposit):
            mask = deposit64(arg_info(op->args[1])->mask,
                             op->args[3], op->args[4],
                             arg_info(op->args[2])->mask);
            break;

        CASE_OP_32_64(extract):
            mask = extract64(arg_info(op->args[1])->mask,
                             op->args[2], op->args[3]);
            if (op->args[2] == 0) {
                affected = arg_info(op->args[1])->mask & ~mask;
            }
            break;
        CASE_OP_32_64(sextract):
            mask = sextract64(arg_info(op->args[1])->mask,
                              op->args[2], op->args[3]);
            if (op->args[2] == 0 && (tcg_target_long)mask >= 0) {
                affected = arg_info(op->args[1])->mask & ~mask;
            }
            break;

        CASE_OP_32_64(or):
        CASE_OP_32_64(xor):
            mask = arg_info(op->args[1])->mask | arg_info(op->args[2])->mask;
            break;

        case INDEX_op_clz_i32:
        case INDEX_op_ctz_i32:
            mask = arg_info(op->args[2])->mask | 31;
            break;

        case INDEX_op_clz_i64:
        case INDEX_op_ctz_i64:
            mask = arg_info(op->args[2])->mask | 63;
            break;

        case INDEX_op_ctpop_i32:
            mask = 32 | 31;
            break;
        case INDEX_op_ctpop_i64:
            mask = 64 | 63;
            break;

        CASE_OP_32_64(setcond):
        case INDEX_op_setcond2_i32:
            mask = 1;
            break;

        CASE_OP_32_64(movcond):
            mask = arg_info(op->args[3])->mask | arg_info(op->args[4])->mask;
            break;

        CASE_OP_32_64(ld8u):
            mask = 0xff;
            break;
        CASE_OP_32_64(ld16u):
            mask = 0xffff;
            break;
        case INDEX_op_ld32u_i64:
            mask = 0xffffffffu;
            break;

        CASE_OP_32_64(qemu_ld):
            {
                TCGMemOpIdx oi = op->args[nb_oargs + nb_iargs];
                MemOp mop = get_memop(oi);
                if (!(mop & MO_SIGN)) {
                    mask = (2ull << ((8 << (mop & MO_SIZE)) - 1)) - 1;
                }
            }
            break;

        default:
            break;
        }

        /* 32-bit ops generate 32-bit results.  For the result is zero test
           below, we can ignore high bits, but for further optimizations we
           need to record that the high bits contain garbage.  */
        partmask = mask;
        if (!(def->flags & TCG_OPF_64BIT)) {
            mask |= ~(tcg_target_ulong)0xffffffffu;
            partmask &= 0xffffffffu;
            affected &= 0xffffffffu;
        }

        if (partmask == 0) {
            tcg_debug_assert(nb_oargs == 1);
            tcg_opt_gen_movi(op, op->args[0], 0);
            continue;
        }
        if (affected == 0) {
            tcg_debug_assert(nb_oargs == 1);
            tcg_opt_gen_mov(op, op->args[0], op->args[1]);
            continue;
        }

        switch (opc) {
        case INDEX_op_discard:
            /* Discard any INDIRECTION on OARG.  */
            ts_set_indirection(arg_temp(op->args[0]), NULL);
            break;

        case INDEX_op_call:
            tmp = op->args[nb_oargs + nb_iargs + 1];
            if (tmp != TCG_CALL_NO_RWG_SE && tmp != TCG_CALL_NO_WG_SE) {
                for (i = 0; i < s->nb_globals; i++) {
                    /* Discard any INDIRECTION on GLOBALs.  */
                    if ((ts = &s->temps[i])->kind == TEMP_GLOBAL) {
                        ts_set_indirection(ts, NULL);
                    }
                }
            }
            goto do_default;

        default:
        do_default:
            /* Frontend codegen should always treat TEMP_NORMALs as being
             * uninitialized at the entry of basic blocks, and initialize
             * them with other kinds of temporaries before using, as will
             * be enforced by tcg_reg_alloc_*. Therefore, it suffices to
             * clear only the INDIRECTION of PHIs to stop copy propagation.  */
            if (def->flags & TCG_OPF_BB_END) {
                for (i = 0; i < s->nb_temps; i++) {
                    if (temp_phi((ts = &s->temps[i]))) {
                        ts_set_indirection(ts, NULL);
                    }
                }
            } else {
                for (i = 0; i < nb_oargs; i++) {
                    init_ots_info(op, i);
                    /* Save the corresponding known-zero bits mask for the
                     * first output argument (only one supported so far).  */
                    arg_info(op->args[0])->mask = mask;
                }
            }
            break;
        }

        /* Eliminate duplicate and redundant fence instructions.  */
        if (prev_mb) {
            switch (opc) {
            case INDEX_op_mb:
                /* Merge two barriers of the same type into one,
                 * or a weaker barrier into a stronger one,
                 * or two weaker barriers into a stronger one.
                 *   mb X; mb Y => mb X|Y
                 *   mb; strl => mb; st
                 *   ldaq; mb => ld; mb
                 *   ldaq; strl => ld; mb; st
                 * Other combinations are also merged into a strong
                 * barrier.  This is stricter than specified but for
                 * the purposes of TCG is better than not optimizing.
                 */
                prev_mb->args[0] |= op->args[0];
                tcg_op_remove(s, op);
                break;

            default:
                /* Opcodes that end the block stop the optimization.  */
                if ((def->flags & TCG_OPF_BB_END) == 0) {
                    break;
                }
                /* fallthru */
            case INDEX_op_qemu_ld_i32:
            case INDEX_op_qemu_ld_i64:
            case INDEX_op_qemu_st_i32:
            case INDEX_op_qemu_st_i64:
            case INDEX_op_call:
                /* Opcodes that touch guest memory stop the optimization.  */
                prev_mb = NULL;
                break;
            }
        } else if (opc == INDEX_op_mb) {
            prev_mb = op;
        }
    done_this_op:
        ;
    }
}

// #define DEBUG_TCG_SSA

#ifdef DEBUG_TCG_SSA
static void tcg_opt_check_ssa(TCGContext *s)
{
    TCGOp *op;
    size_t i;

    for (i = 0; i < s->nb_temps; i++) {
        s->temps[i].state = 0;
    }

    QTAILQ_FOREACH(op, &s->ops, link) {
        uint8_t nb_oargs, nb_iargs;
        TCGTemp *ts;

        if (op->opc == INDEX_op_call) {
            nb_oargs = TCGOP_CALLO(op);
            nb_iargs = TCGOP_CALLI(op);
        } else {
            const TCGOpDef *def = &tcg_op_defs[op->opc];
            nb_oargs = def->nb_oargs;
            nb_iargs = def->nb_iargs;
        }

        for (i = 0; i < nb_oargs; i++) {
            ts = arg_temp(op->args[i]);
            switch (ts->kind) {
            case TEMP_NORMAL:
                tcg_debug_assert(temp_definition(ts) == op);
                tcg_debug_assert(++ts->state == 1);
                break;
            case TEMP_LOCAL:
            case TEMP_GLOBAL:
                tcg_debug_assert(op->opc == type_to_mov_opc(ts->type) ||
                                 op->opc == INDEX_op_discard);
                break;
            default:
                g_assert_not_reached();
            }
        }
        for ( ; i < nb_oargs + nb_iargs; i++) {
            ts = arg_temp(op->args[i]);
            switch (ts->kind) {
            case TEMP_NORMAL:
                tcg_debug_assert(ts->state == 1);
                break;
            case TEMP_LOCAL:
            case TEMP_GLOBAL:
                tcg_debug_assert(op->opc == type_to_mov_opc(ts->type));
                break;
            case TEMP_FIXED:
            case TEMP_CONST:
                break;
            default:
                g_assert_not_reached();
            }
        }
    }
}
#endif

void tcg_optimize(TCGContext *s)
{
    tcg_opt_convert_to_ssa_and_peephole(s);
#ifdef DEBUG_TCG_SSA
    tcg_opt_check_ssa(s);
#endif
}

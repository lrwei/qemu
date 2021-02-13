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
static const TCGOpcode INDEX_op_mov_tl = INDEX_op_mov_i32;
static const TCGOpcode INDEX_op_add_tl = INDEX_op_add_i32;
static const TCGOpcode INDEX_op_and_tl = INDEX_op_and_i32;
#else
static const TCGOpcode INDEX_op_mov_tl = INDEX_op_mov_i64;
static const TCGOpcode INDEX_op_add_tl = INDEX_op_add_i64;
static const TCGOpcode INDEX_op_and_tl = INDEX_op_and_i64;
#endif

/* Illustration on data structures used in local value numbering algorithm:
 *
 * 1. The NUMBER of current VARIABLE is recorded in `ts->state` field, its
 *    being zero means this VARIABLE has not been initialized. NUMBER is
 *    the index of VALUE which is hold in CANONICAL VARIABLE sits at
 *    `g_array_index(tcg_ctx->num2value, NUMBER - 1)`.
 * 2. For all CANONICAL (and only CANONICAL) VARIABLEs, `ts->state_ptr` holds
 *    the information of its VALUE.
 * 3. Due to the caching mechanism used by tcg_temp_new_internal(), CANONICAL
 *    VARIABLEs are rewritten very frequently, therefore, transfering of its
 *    VALUE to another temporary happens only when that VALUE is explicitly
 *    requested by further ops.  */

#define OPT_MAX_OPC_PARAM_IARGS 2
typedef struct TCGValue {
    TCGOpcode opc : 8;
    uint16_t numbers[OPT_MAX_OPC_PARAM_IARGS];
} TCGValue;

typedef struct TempOptInfo {
    uint64_t mask;
    TCGValue *value;
    bool reassociated;
    int64_t offset;
} TempOptInfo;

typedef struct ValueNumberingEntry {
    TCGTemp *canonical;
    TCGOp *redef_op;
    TempOptInfo *info;
    uint16_t the_address;
} ValueNumberingEntry;

static inline bool ts_is_initialized(TCGTemp *ts)
{
    return ts->state != 0;
}

static inline bool ts_is_canonical(TCGTemp *ts)
{
    return ts_is_initialized(ts) && ts->state_ptr;
}

static inline TempOptInfo *ts_info(TCGTemp *ts)
{
    tcg_debug_assert(ts_is_canonical(ts));
    return ts->state_ptr;
}

static inline TempOptInfo *arg_info(TCGArg arg)
{
    return ts_info(arg_temp(arg));
}

static inline uint16_t ts_number(TCGTemp *ts)
{
    tcg_debug_assert(ts_is_initialized(ts));
    tcg_debug_assert(ts->state == (uint16_t) ts->state);
    return ts->state;
}

static inline void ts_set_number(TCGTemp *ts, uintptr_t number)
{
    ts->state = number;
}

static inline void ts_set_uninitialized(TCGTemp *ts)
{
    ts_set_number(ts, 0);
    ts->state_ptr = NULL;
}

static inline bool ts_are_copies(TCGTemp *dst_ts, TCGTemp *src_ts)
{
    /* Source temporary should have been initialized.  */
    tcg_debug_assert(ts_is_initialized(src_ts));

    if (!ts_is_initialized(dst_ts)) {
        return false;
    }
    return ts_number(dst_ts) == ts_number(src_ts);
}

static inline bool args_are_copies(TCGArg arg1, TCGArg arg2)
{
    return ts_are_copies(arg_temp(arg1), arg_temp(arg2));
}

static inline bool ts_is_const(TCGTemp *ts)
{
    return ts->kind == TEMP_CONST;
}

static inline bool arg_is_const(TCGArg arg)
{
    return ts_is_const(arg_temp(arg));
}

static inline uint64_t ts_value(TCGTemp *ts)
{
    tcg_debug_assert(ts_is_const(ts));
    return ts->val;
}

static inline uint64_t arg_value(TCGArg arg)
{
    return ts_value(arg_temp(arg));
}

static inline ValueNumberingEntry *num2vne(uint16_t number)
{
    /* Zero is used to indicate uninitialized variable.  */
    tcg_debug_assert(number != 0);
    return &g_array_index(tcg_ctx->num2value, ValueNumberingEntry, number - 1);
}

static void tcg_opt_number_value(GArray *num2value, TCGTemp *ts)
{
    ValueNumberingEntry vne = {
        .canonical = ts,
        .info = ts->state_ptr,
    };

    /* VALUE numbered N actually uses entrys[N - 1], see also num2vne().  */
    g_array_append_val(num2value, vne);
    ts_set_number(ts, num2value->len);
}

static void tcg_opt_canonical_save(TCGTemp *ts, TCGOp *redef_op)
{
    ValueNumberingEntry *vne = num2vne(ts_number(ts));

    tcg_debug_assert(ts == vne->canonical);
    tcg_debug_assert(vne->info == ts_info(ts));
    vne->redef_op = redef_op;
    ts_set_uninitialized(ts);
}

static void init_ts_info(TCGTemp *ts, TCGOp *def_op)
{
    TempOptInfo *info;

    /* Filter possible TCG_CALL_DUMMY_ARG.  */
    if (unlikely(ts == NULL)) {
        return;
    } else if (!def_op && ts_is_initialized(ts)) {
        return;
    } else if (ts_is_canonical(ts)) {
        tcg_opt_canonical_save(ts, def_op);
    }

    tcg_debug_assert(ts->state_ptr == NULL);
    ts->state_ptr = info = tcg_malloc(sizeof(TempOptInfo));

    if (ts_is_const(ts)) {
        info->mask = ts_value(ts);
        if (TCG_TARGET_REG_BITS > 32 && ts->type == TCG_TYPE_I32) {
            /* High bits of a 32-bit quantity are garbage.  */
            info->mask |= ~0xffffffffull;
        }
    } else {
        info->mask = -1;
    }
    info->value = NULL;

    tcg_opt_number_value(tcg_ctx->num2value, ts);
}

static void init_arg_info(TCGArg arg, TCGOp *def_op)
{
    return init_ts_info(arg_temp(arg), def_op);
}

static inline TCGArg tcg_opt_constant_new(TCGType type, int64_t value)
{
    TCGTemp *ts = tcg_constant_internal(type, value);
    init_ts_info(ts, NULL);
    return temp_arg(ts);
}

static bool tcg_opt_gen_mov__unchecked(TCGOp *op, TCGArg dst, TCGArg src)
{
    TCGTemp *dst_ts = arg_temp(dst);
    TCGTemp *src_ts = arg_temp(src);
    const TCGOpDef *def = &tcg_op_defs[op->opc];
    TCGOpcode opc;

    if (ts_are_copies(dst_ts, src_ts)) {
        tcg_op_remove(tcg_ctx, op);
        return true;
    }

    /* No type information can be inferred from this shit.  */
    tcg_debug_assert(op->opc != INDEX_op_discard);

    if (def->flags & TCG_OPF_VECTOR) {
        opc = INDEX_op_mov_vec;
    } else if (def->flags & TCG_OPF_64BIT) {
        opc = INDEX_op_mov_i64;
    } else {
        opc = INDEX_op_mov_i32;
    }
    op->opc = opc;
    /* TCGOP_VECL and TCGOP_VECE remain unchanged.  */
    op->args[0] = dst;
    op->args[1] = src;

    if (likely(dst_ts->type == src_ts->type)) {
        if (ts_is_canonical(dst_ts)) {
            tcg_opt_canonical_save(dst_ts, op);
        }
        /* Moving between the same type only serves as a propagation
         * of value number.  */
        ts_set_number(dst_ts, ts_number(src_ts));

        /* Prefer using globals as CANONICAL VARIABLE.  */
        if (dst_ts->kind > src_ts->kind) {
            ValueNumberingEntry *vne = num2vne(ts_number(src_ts));
            dst_ts->state_ptr = ts_info(src_ts);
            src_ts->state_ptr = NULL;
            vne->canonical = dst_ts;
        }
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

    /* Convert movi to mov with constant temp.  */
    tcg_opt_gen_mov(op, dst, tcg_opt_constant_new(type, value));
}

static TCGOp *tcg_opt_reluctantly_dup_op_with_caution(TCGOp *op)
{
    TCGOpcode opc = op->opc;

    if (unlikely(opc == INDEX_op_discard)) {
        TCGTemp *ts = arg_temp(op->args[0]);

        if (ts->type == TCG_TYPE_I32) {
            opc = INDEX_op_mov_i32;
        } else if (ts->type == TCG_TYPE_I64) {
            opc = INDEX_op_mov_i64;
        } else {
            /* Would this ever happen?  */
            opc = INDEX_op_mov_vec;
        }
    }

    return tcg_op_insert_before(NULL, op, opc);
}

static void tcg_opt_reluctantly_redo_copy_propagation(TCGOp *op, TCGTemp *old,
                                                      TCGTemp *new)
{
    const TCGOpDef *def = &tcg_op_defs[op->opc];
    uint8_t i, nb_oargs, nb_iargs;

    if (unlikely(op->opc == INDEX_op_call)) {
        nb_oargs = TCGOP_CALLO(op);
        nb_iargs = TCGOP_CALLI(op);
    } else {
        nb_oargs = def->nb_oargs;
        nb_iargs = def->nb_iargs;
    }

    for (i = nb_oargs; i < nb_oargs + nb_iargs; i++) {
        if (op->args[i] == temp_arg(old)) {
            op->args[i] = temp_arg(new);
        }
    }
}

static void tcg_opt_canonical_restore(ValueNumberingEntry *vne, uint16_t number)
{
    /* Caching mechanism used by tcg_temp_new_internal() guarantees that
     * TCGTemps never change their type, so we can safely use the old type
     * when creating a new one.  */
    TCGTemp *ts = tcg_opt_temp_new(vne->canonical->type);
    TCGOp *op;

    /* Hack in order to reuse logic in tcg_opt_gen_mov(). Note that mov_vec
     * is reg-alloc'ed without using TCGOP_VECL/E, don't bother coping those
     * stuffs.  */
    op = tcg_opt_reluctantly_dup_op_with_caution(vne->redef_op);
    tcg_debug_assert(!ts_is_canonical(ts));
    tcg_opt_gen_mov(op, temp_arg(ts), temp_arg(vne->canonical));

    /* Fix the propagated value number since that of `vne->canonical` would
     * have been changed by this time, fix it.  */
    ts_set_number(ts, number);

    /* Prefer:  mov_i64 tmp1, tmp0      than:   mov_i64 tmp1, tmp0
     *          add_i64 tmp0, tmp1, $8          add_i64 tmp0, tmp0, $8
     * since the latter one will generates 1 more register movement.  */
    tcg_opt_reluctantly_redo_copy_propagation(vne->redef_op, vne->canonical,
                                              ts);

    /* Promote `ts` to be the new CANONICAL VARIABLE.  */
    ts->state_ptr = vne->info;
    vne->canonical = ts;

    /* CANONICAL VARIABLE has been restored.  */
    vne->redef_op = NULL;
}

static TCGTemp *num2var(uint16_t number)
{
    ValueNumberingEntry *vne = num2vne(number);

    if (unlikely(vne->redef_op)) {
        tcg_opt_canonical_restore(vne, number);
    }
    return vne->canonical;
}

static bool value_has_constant_offset(TCGValue *value, uint64_t *offset,
                                      bool check)
{
    TCGTemp *ts;

    if (check && (!value || value->opc != INDEX_op_add_tl)) {
        return false;
    }

    /* Hack: .canonical fields of constant temporaries are
     * always valid, and is never going to change.  */
    ts = num2vne(value->numbers[1])->canonical;
    if (!ts_is_const(ts)) {
        return false;
    } else {
        *offset = ts_value(ts);
        return true;
    }
}

static void tcg_opt_aggregate_offset(TCGOp *op)
{
    TCGValue *value = arg_info(op->args[1])->value;
    uint64_t offset, offset2;

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

    if (value) {
        switch (value->opc) {
        CASE_OP_32_64(add):
            if (value_has_constant_offset(value, &offset2, false)) {
                offset += offset2;
                op->args[1] = temp_arg(num2var(value->numbers[0]));
            }
            if (value->opc == INDEX_op_add_i32
                && unlikely(offset != (int32_t) offset)) {
                offset = (int32_t) offset;
            }
            break;
        CASE_OP_32_64(sub):
            /* Previous SUBI operations should have been transformed
             * into ADDIs.  */
            tcg_debug_assert(!value_has_constant_offset(value, NULL, false));
            break;
        default:
            break;
        }
    }

    op->args[2] = tcg_opt_constant_new(arg_temp(op->args[1])->type, offset);
}

#define SPECULATION_THRESHOLD           (1 << (TARGET_PAGE_BITS - 2))
static void tcg_opt_reassociate_address_finalize(TCGOp *op)
{
    TCGTemp *addr = arg_temp(op->args[2]);
    TempOptInfo *info = ts_info(addr);
    TCGArg _base, _offset;
    ValueNumberingEntry *vne;
    uint64_t offset, offset2;
    TCGOp *op2, *op3;

    if (ts_is_const(addr)) {
        /* Constant address ignored for the time being.  */
        goto not_found;
    } else if (!value_has_constant_offset(info->value, &offset, true)) {
        /* Non-constant offset ignored for the time being.  */
        vne = num2vne(ts_number(addr));
        offset = 0;
    } else {
        vne = num2vne(info->value->numbers[0]);
    }

    if (vne->the_address != 0) {
        _base = temp_arg(num2var(vne->the_address));
        if (value_has_constant_offset(arg_info(_base)->value, &offset2, true)) {
            offset -= offset2;
        }
        if (unlikely(llabs(offset) > SPECULATION_THRESHOLD)) {
            goto not_found;
        }
        info->reassociated = true;
        info->offset = offset;
    } else {
        vne->the_address = ts_number(addr);
    not_found:
        _base = temp_arg(addr);
        offset = 0;
        info->reassociated = false;
    }
    _offset = tcg_opt_constant_new(TCG_TYPE_TL, offset);

    /* ts_set_number() must be called through tcg_opt_gen_mov(), as
     * temporaries `base` and `offset` maybe canonical variables.  */
    op2 = tcg_op_insert_before(NULL, op, INDEX_op_mov_tl);
    op3 = tcg_op_insert_before(NULL, op, INDEX_op_mov_tl);
    tcg_opt_gen_mov(op3, op->args[1], _offset);
    tcg_opt_gen_mov(op2, op->args[0], _base);
}

static bool tcg_opt_extract_tag_finalize(TCGOp *op)
{
    TempOptInfo *info = arg_info(op->args[1]);
    MemOp memop = op->args[2];
    uint32_t a_bits = get_alignment_bits(memop);
    uint32_t s_bits = memop & MO_SIZE;
    uint32_t a_mask = (1 << a_bits) - 1;
    uint32_t s_mask = (1 << s_bits) - 1;
    bool rewind_needed = false;

    if (a_bits >= s_bits) {
        /* Alignment check implies the cross-page check for accesses with
         * natural (or more strict) alignment.  */
    } else if (!info->reassociated || info->offset >= 0) {
        TCGOp *op2 = tcg_op_insert_before(NULL, op, INDEX_op_add_tl);

        /* Otherwise, we pad the address to the last byte of the access WITH
         * THE ASSUMPTION THAT THE ADDRESS ITSELF IS ALIGNED, so that further
         * comparison fails if EITHER of the requirement is not met.  */
        op2->args[0] = op->args[0];
        op2->args[1] = op->args[1];
        op2->args[2] = tcg_opt_constant_new(TCG_TYPE_TL, s_mask - a_mask);

        rewind_needed = true;
        op->args[1] = op->args[0];
    } else {
        /* Special care must be taken after speculation comes into play,
         * since a wrong speculation that actually fall on the previous
         * page (which must have NEGATIVE offset) will pass the guard if
         * it happens to be a cross-page access.
         * To address this problem, speculation with negative offset only
         * checks the aligned-ness requirement, WITH THE ASSUMPTION THE
         * ADDRESS DOES FALL ON THE SAME PAGE, so that further comparison
         * fails if EITHER of the requirement is not met.  */

        /* If the negative offset is not large enough to guarantee the
         * within-ness, then we instead require the access itself to be
         * natually aligned, which unfortunately is quite unlikely to
         * hold.  */
        if (unlikely(info->offset + s_mask > 0)) {
            a_mask = s_mask;
        }
    }

    op->opc = INDEX_op_and_tl;
    op->args[2] = tcg_opt_constant_new(TCG_TYPE_TL, TARGET_PAGE_MASK | a_mask);
    return rewind_needed;
}

static inline bool try_common_subexpression_elimination(const TCGOpDef *def,
                                                        const TCGOp *op)
{
    if (def->nb_oargs == 1 && def->nb_iargs > 0
        && def->nb_iargs + def->nb_cargs <= OPT_MAX_OPC_PARAM_IARGS
        && !(def->flags & TCG_OPF_VECTOR)) {
        if (op && def->nb_cargs > 0) {
            TCGArg carg = op->args[1 + def->nb_iargs];
            tcg_debug_assert(def->nb_cargs == 1);
            return likely(carg == (int16_t) carg);
        } else {
            return true;
        }
    }
    return false;
}

static TCGValue *tcg_opt_make_value(TCGOp *op, TCGValue *value)
{
    const TCGOpDef *def = &tcg_op_defs[op->opc];
    size_t i;

    tcg_debug_assert(try_common_subexpression_elimination(def, NULL));

    if (!value) {
        value = tcg_malloc(sizeof(TCGValue));
    }

    value->opc = op->opc;
    for (i = 1; i < 1 + def->nb_iargs; i++) {
        value->numbers[i - 1] = ts_number(arg_temp(op->args[i]));
    }
    for ( ; i < 1 + def->nb_iargs + def->nb_cargs; i++) {
        tcg_debug_assert(op->args[i] == (int16_t) op->args[i]);
        value->numbers[i - 1] = op->args[i];
    }

    return value;
}

static void tcg_opt_record_value(GHashTable *value2num, TCGValue **value,
                                 TCGTemp *ts)
{
    tcg_debug_assert(g_hash_table_insert(value2num, *value,
                                         GSIZE_TO_POINTER(ts_number(ts))));
    ts_info(ts)->value = *value;
    /* Consume the value.  */
    *value = NULL;
}

/* Fake boost::hash_combine(), in which 0x9e3779b9 equals 2^32 / phi.  */
static inline void hash_combine(uint32_t *seed, uint32_t value)
{
    *seed ^= value + 0x9e3779b9 + (*seed << 6) + (*seed >> 2);
}

/* Converts a TCGOp to a 32-bit hash value.
 *
 * All information isn't encoded for simplicity, indeed, the first constant
 * input argument OR the second variable input argument is encoded, based on
 * the observation that they don't show up together very often, and constant
 * offset is very important to distinguish ld operations.  */
static guint tcg_op_hash(gconstpointer key)
{
    const TCGValue *value = key;
    const TCGOpDef *def = &tcg_op_defs[value->opc];
    uint32_t hash = value->numbers[0];

    tcg_debug_assert(try_common_subexpression_elimination(def, NULL));

    if (def->nb_cargs > 0 || def->nb_iargs > 1) {
        hash_combine(&hash, value->numbers[1]);
    }
    hash_combine(&hash, value->opc);

    return hash;
}

/* Check that 2 TCGValues do equal.  */
static gboolean tcg_op_equal(gconstpointer key, gconstpointer key2)
{
    const TCGValue *value = key, *value2 = key2;
    const TCGOpDef *def = &tcg_op_defs[value->opc];
    size_t i;

    tcg_debug_assert(try_common_subexpression_elimination(def, NULL));

    if (value->opc != value2->opc) {
        return FALSE;
    }

    for (i = 0; i < def->nb_iargs + def->nb_cargs; i++) {
        if (value->numbers[i] != value2->numbers[i]) {
            return FALSE;
        }
    }
    return TRUE;
}

void tcg_opt_vn_initialize(TCGContext *s)
{
    s->value2num = g_hash_table_new(tcg_op_hash, tcg_op_equal);
    s->num2value = g_array_sized_new(FALSE, FALSE,
                                     sizeof(ValueNumberingEntry), 64);
}

void tcg_opt_vn_reset(TCGContext *s)
{
    g_hash_table_remove_all(s->value2num);
    g_array_set_size(s->num2value, 0);
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

void tcg_optimize(TCGContext *s)
{
    TCGOp *op, *op_next, *prev_mb = NULL;
    size_t i;
    TCGValue *value = NULL;

    for (i = 0; i < s->nb_temps; i++) {
        ts_set_uninitialized(&s->temps[i]);
    }

    QTAILQ_FOREACH_SAFE(op, &s->ops, link, op_next) {
        uint64_t mask, partmask, affected, tmp;
        uint8_t nb_oargs, nb_iargs;
        TCGOpcode opc = op->opc;
        const TCGOpDef *def = &tcg_op_defs[opc];
        TCGTemp *ts;

        /* Count the arguments, and initialize all input arguments,
         * this will catch all variables that are read before written to.  */
        if (opc == INDEX_op_call) {
            nb_oargs = TCGOP_CALLO(op);
            nb_iargs = TCGOP_CALLI(op);
        } else {
            nb_oargs = def->nb_oargs;
            nb_iargs = def->nb_iargs;
        }
        for (i = nb_oargs; i < nb_oargs + nb_iargs; i++) {
            init_arg_info(op->args[i], NULL);
        }

        /* Do copy propagation.  */
        for (i = nb_oargs; i < nb_oargs + nb_iargs; i++) {
            ts = arg_temp(op->args[i]);
            /* Filter possible TCG_CALL_DUMMY_ARG.  */
            if (ts) {
                tcg_debug_assert(ts_is_initialized(ts));
                op->args[i] = temp_arg(num2var(ts_number(ts)));
            }
        }

        switch (opc) {
        case INDEX_op_reassociate_address:
            tcg_opt_reassociate_address_finalize(op);
            continue;
        case INDEX_op_extract_tag:
            if (tcg_opt_extract_tag_finalize(op)) {
                /* Rewind to process the newly inserted op.  */
                op_next = QTAILQ_PREV(op, link);
                continue;
            }
            opc = op->opc;
            break;
        case INDEX_op_tlb_check:
            if (arg_info(op->args[2])->reassociated) {
                op->opc = TARGET_LONG_BITS == 32 ? INDEX_op_guard_i32
                                                 : INDEX_op_guard_i64;
            }
            continue;
        default:
            break;
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

        /* Do common subexpression elimination, or register new value into
         * the hash table. Several opcode are specially handled to preserve
         * the correctness.  */
        switch (opc) {
        case INDEX_op_call:
            /* Call to pure functions doesn't flush the optimization status,
             * but is still not numbered.  */
            if (op->args[nb_oargs + nb_iargs + 1] == TCG_CALL_NO_RWG_SE) {
                goto reset;
            }
            goto reset_all;

        case INDEX_op_discard:
        CASE_OP_32_64(qemu_ld):
        CASE_OP_32_64(ld8u):
        CASE_OP_32_64(ld8s):
        CASE_OP_32_64(ld16u):
        CASE_OP_32_64(ld16s):
        CASE_OP_32_64_VEC(ld):
        case INDEX_op_ld32u_i64:
        case INDEX_op_ld32s_i64:
            goto reset;

        default:
            if (try_common_subexpression_elimination(def, op)) {
                /* This variable retains its value throughout the loop.  */
                value = tcg_opt_make_value(op, value);
                i = GPOINTER_TO_SIZE(g_hash_table_lookup(s->value2num, value));
                if (i) {
                    tcg_opt_gen_mov(op, op->args[0], temp_arg(num2var(i)));
                } else {
                    ts = arg_temp(op->args[0]);
                    init_ts_info(ts, op);
                    /* Save the corresponding known-zero bits mask for the
                     * first output argument (only one supported so far).  */
                    ts_info(ts)->mask = mask;

                    tcg_opt_record_value(s->value2num, &value, ts);
                }
            } else if (def->flags & TCG_OPF_BB_END) {
        reset_all:
                /* TODO: When incorporating tracing compilation, we need to
                 * properly handle goto_tb and goto_ptr. For now, just reset
                 * everything.  */
                for (i = 0; i < s->nb_temps; i++) {
                    ts_set_uninitialized(&s->temps[i]);
                }
                tcg_opt_vn_reset(s);
            } else {
        reset:
                for (i = 0; i < nb_oargs; i++) {
                    init_arg_info(op->args[i], op);
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
    }
}

/*
 * Generic intermediate code generation.
 *
 * Copyright (C) 2016-2017 Lluís Vilanova <vilanova@ac.upc.edu>
 *
 * This work is licensed under the terms of the GNU GPL, version 2 or later.
 * See the COPYING file in the top-level directory.
 */

#include "qemu/osdep.h"
#include "qemu/error-report.h"
#include "cpu.h"
#include "tcg/tcg.h"
#include "tcg/tcg-op.h"
#include "exec/exec-all.h"
#include "exec/gen-icount.h"
#include "exec/log.h"
#include "exec/translator.h"
#include "exec/plugin-gen.h"
#include "sysemu/replay.h"

/* Pairs with tcg_clear_temp_count.
   To be called by #TranslatorOps.{translate_insn,tb_stop} if
   (1) the target is sufficiently clean to support reporting,
   (2) as and when all temporaries are known to be consumed.
   For most targets, (2) is at the end of translate_insn.  */
void translator_loop_temp_check(DisasContextBase *db)
{
    if (tcg_check_temp_count()) {
        qemu_log("warning: TCG temporary leaks before "
                 TARGET_FMT_lx "\n", db->pc_next);
    }
}

static void translator_loop_tb_finalize(CPUArchState *env, TranslationBlock *tb)
{
    target_ulong virt_page2 = (tb->pc + tb->size - 1) & TARGET_PAGE_MASK;
    TCGOp *op;

    /* In !trace mode, page_addr[0] is filled in tb_gen_code(), otherwise
     * both of page_addr[] should have been filled.  */
    if (tb->page_addr[0] == -1 || (tb->pc & TARGET_PAGE_MASK) == virt_page2) {
        if (!tcg_ctx->trace) {
            tb->page_addr[1] = -1;
        } else {
            tcg_debug_assert(tb->page_addr[0] != -1 && tb->page_addr[1] == -1);
        }
        return;
    }

    if (!tcg_ctx->trace) {
        tb->page_addr[1] = get_page_addr_code(env, virt_page2);
        /* This would be too damn weird.  */
        g_assert(tb->page_addr[1] != -1);

        /* Insert iTLB check stub after entry INSN_START to guard against cross
         * page TB's being invalidated due to partially updated memory mapping,
         * won't be skipped.  */
        QTAILQ_FOREACH(op, &tcg_ctx->ops, link) {
            if (op->opc == INDEX_op_insn_start) {
                break;
            }
        }
    } else {
        g_assert_not_reached();
    }

    tcg_insert_itlb_check_stub(tcg_ctx, op, tb, false);
    /* These two should be equal.  */
    tcg_debug_assert(QTAILQ_NEXT(op, link)->args[2] == cpu_mmu_index(env, 1));
}

void translator_loop(const TranslatorOps *ops, DisasContextBase *db,
                     CPUState *cpu, TranslationBlock *tb, int max_insns)
{
    int bp_insn = 0;
    bool plugin_enabled, tb_start_emitted = false, tb_started = false;
    uint32_t bailout_n = tb_cflags(tb) & CF_BAILOUT_MASK;

    /* Initialize DisasContext */
    db->tb = tb;
    db->pc_first = tb->pc;
    db->pc_next = db->pc_first;
    db->is_jmp = DISAS_NEXT;
    db->num_insns = 0;
    db->max_insns = max_insns;
    db->singlestep_enabled = cpu->singlestep_enabled;

    ops->init_disas_context(db, cpu);
    tcg_debug_assert(db->is_jmp == DISAS_NEXT);  /* no early exit */

    /* Reset the temp count so that we can identify leaks */
    tcg_clear_temp_count();

    /* Start translating.  */
    if (bailout_n) {
        TCGv_ptr bailout_tb = tcg_const_ptr((uintptr_t) tb);

        /* BAILOUT TBs shall restore state at TB entry. Most targets don't
         * care the correctness of the state within the middle of TB, and
         * get corresponding values through tb->flags (so restoration only
         * need to happen once at compile time). However, there does exist
         * situations where this restoration is necessary, e.g. CC_OP for
         * x86 target.  */
        gen_helper_restore_state_from_bailout(cpu_env, bailout_tb);

        /* CF_BAILOUT_1 stands for bailout for TLB_GUARD, which by definition
         * must start from the same page. CF_BAILOUT_2 is for GUARDs that MAY
         * start from a different page, and CF_BAILOUT_3 is for all else.  */
        switch (bailout_n) {
        case CF_BAILOUT_1:
            /* Bailout TB of TLB_GUARD must use monolithic ldst, and
             * will not be profiled or optimized again. Neither does
             * it need interrupt checking stub, as CF_BAILOUT TB can
             * not form loop themselves.  */

            /* TCG can't be of trace recording mode at here, for:
             * 1. The TB itself doesn't do profiling, so no early exit or
             *    retranslation.
             * 2. Bailout TB can only be executed from side exit of traces,
             *    which should have terminated the trace recording mode.  */
            tcg_debug_assert(!tcg_ctx->trace);
            break;
        case CF_BAILOUT_2:
        case CF_BAILOUT_3:
            g_assert_not_reached();
            if (!tcg_ctx->trace) {
                // gen_helper_profile_tb(cpu_env, bailout_tb);
                gen_tb_start(db->tb);
                tb_start_emitted = true;
            }
            break;
        default:
            g_assert_not_reached();
        }
        tcg_temp_free_ptr(bailout_tb);
    } else if (!tcg_ctx->trace) {
        /* Trace (except for BAILOUT ones) must have TB prologue / epilogue,
         * so that other rounds of trace recording can stop on encountering
         * existing traces. However, TB retranslated during trace recording
         * won't have their own ones, the sole copy will be emitted only at
         * trace finalization step.  */
        gen_tb_start(db->tb);
        tb_start_emitted = true;
    }
    tcg_debug_assert(db->is_jmp == DISAS_NEXT);  /* no early exit */

    plugin_enabled = plugin_gen_tb_start(cpu, tb);

    while (true) {
        db->num_insns++;
        ops->insn_start(db, cpu);
        if (!tb_started) {
            /* Must be inserted under some INSN_START op, for proper restore
             * of CPU state. (Have to use register map encoded in INSN_START,
             * not implemented yet).  */
            if (bailout_n == CF_BAILOUT_2) {
                tcg_insert_itlb_check_stub(tcg_ctx, tcg_last_op(), tb, true);
            }
            /* Target-specific tb_start() should always be executed, and
             * shall be excluded from the TB prologue.  */
            ops->tb_start(db, cpu);
            tb_started = true;
        }
        tcg_debug_assert(db->is_jmp == DISAS_NEXT);  /* no early exit */

        if (plugin_enabled) {
            plugin_gen_insn_start(cpu, db);
        }

        /* Pass breakpoint hits to target for further processing */
        if (!db->singlestep_enabled
            && unlikely(!QTAILQ_EMPTY(&cpu->breakpoints))) {
            CPUBreakpoint *bp;
            QTAILQ_FOREACH(bp, &cpu->breakpoints, entry) {
                if (bp->pc == db->pc_next) {
                    if (ops->breakpoint_check(db, cpu, bp)) {
                        bp_insn = 1;
                        break;
                    }
                }
            }
            /* The breakpoint_check hook may use DISAS_TOO_MANY to indicate
               that only one more instruction is to be executed.  Otherwise
               it should use DISAS_NORETURN when generating an exception,
               but may use a DISAS_TARGET_* value for Something Else.  */
            if (db->is_jmp > DISAS_TOO_MANY) {
                break;
            }
        }

        /* Disassemble one instruction.  The translate_insn hook should
           update db->pc_next and db->is_jmp to indicate what should be
           done next -- either exiting this loop or locate the start of
           the next instruction.  */
        if (db->num_insns == db->max_insns
            && (tb_cflags(db->tb) & CF_LAST_IO)) {
            /* Accept I/O on the last instruction.  */
            gen_io_start();
            ops->translate_insn(db, cpu);
        } else {
            ops->translate_insn(db, cpu);
        }

        /* Stop translation if translate_insn so indicated.  */
        if (db->is_jmp != DISAS_NEXT) {
            break;
        }

        /*
         * We can't instrument after instructions that change control
         * flow although this only really affects post-load operations.
         */
        if (plugin_enabled) {
            plugin_gen_insn_end();
        }

        /* Stop translation if the output buffer is full,
           or we have executed all of the allowed instructions.  */
        if (tcg_op_buf_full() || db->num_insns >= db->max_insns) {
            db->is_jmp = DISAS_TOO_MANY;
            break;
        }
    }

    /* Emit code to exit the TB, as indicated by db->is_jmp.  */
    ops->tb_stop(db, cpu);
    /* Paired with gen_tb_start().  */
    if (tb_start_emitted) {
        gen_tb_end(db->tb, db->num_insns - bp_insn);
    }

    if (plugin_enabled) {
        plugin_gen_tb_end(cpu);
    }

    /* The disas_log hook may use these values rather than recompute.  */
    db->tb->size = db->pc_next - db->pc_first;
    db->tb->icount = db->num_insns;

    translator_loop_tb_finalize(cpu->env_ptr, tb);

#ifdef DEBUG_DISAS
    if (qemu_loglevel_mask(CPU_LOG_TB_IN_ASM)
        && qemu_log_in_addr_range(db->pc_first)) {
        FILE *logfile = qemu_log_lock();
        qemu_log("----------------\n");
        ops->disas_log(db, cpu);
        qemu_log("\n");
        qemu_log_unlock(logfile);
    }
#endif
}

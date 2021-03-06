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

#ifdef CONFIG_DEBUG_TCG
static const char * const tcg_target_reg_names[TCG_TARGET_NB_REGS] = {
#if TCG_TARGET_REG_BITS == 64
    "%rax", "%rcx", "%rdx", "%rbx", "%rsp", "%rbp", "%rsi", "%rdi",
#else
    "%eax", "%ecx", "%edx", "%ebx", "%esp", "%ebp", "%esi", "%edi",
#endif
    "%r8",  "%r9",  "%r10", "%r11", "%r12", "%r13", "%r14", "%r15",
    "%xmm0", "%xmm1", "%xmm2", "%xmm3", "%xmm4", "%xmm5", "%xmm6", "%xmm7",
#if TCG_TARGET_REG_BITS == 64
    "%xmm8", "%xmm9", "%xmm10", "%xmm11",
    "%xmm12", "%xmm13", "%xmm14", "%xmm15",
#endif
};
#endif

static const TCGReg tcg_target_reg_alloc_order[] = {
#if TCG_TARGET_REG_BITS == 64
    TCG_REG_RBP,
    TCG_REG_RBX,
    TCG_REG_R12,
    TCG_REG_R13,
    TCG_REG_R14,
    TCG_REG_R15,
    TCG_REG_R10,
    TCG_REG_R11,
    TCG_REG_R9,
    TCG_REG_R8,
    TCG_REG_RCX,
    TCG_REG_RDX,
    TCG_REG_RSI,
    TCG_REG_RDI,
    TCG_REG_RAX,
#else
    TCG_REG_EBX,
    TCG_REG_ESI,
    TCG_REG_EDI,
    TCG_REG_EBP,
    TCG_REG_ECX,
    TCG_REG_EDX,
    TCG_REG_EAX,
#endif
    TCG_REG_XMM0,
    TCG_REG_XMM1,
    TCG_REG_XMM2,
    TCG_REG_XMM3,
    TCG_REG_XMM4,
    TCG_REG_XMM5,
#ifndef _WIN64
    /* The Win64 ABI has xmm6-xmm15 as caller-saves, and we do not save
       any of them.  Therefore only allow xmm0-xmm5 to be allocated.  */
    TCG_REG_XMM6,
    TCG_REG_XMM7,
#if TCG_TARGET_REG_BITS == 64
    TCG_REG_XMM8,
    TCG_REG_XMM9,
    TCG_REG_XMM10,
    TCG_REG_XMM11,
    TCG_REG_XMM12,
    TCG_REG_XMM13,
    TCG_REG_XMM14,
    TCG_REG_XMM15,
#endif
#endif
};

static const TCGReg tcg_target_call_iarg_regs[] = {
#if TCG_TARGET_REG_BITS == 64
#if defined(_WIN64)
    TCG_REG_RCX,
    TCG_REG_RDX,
#else
    TCG_REG_RDI,
    TCG_REG_RSI,
    TCG_REG_RDX,
    TCG_REG_RCX,
#endif
    TCG_REG_R8,
    TCG_REG_R9,
#else
    /* 32 bit mode uses stack based calling convention (GCC default). */
#endif
};

static const TCGReg tcg_target_call_oarg_regs[] = {
    TCG_REG_EAX,
#if TCG_TARGET_REG_BITS == 32
    TCG_REG_EDX
#endif
};

static const int tcg_target_callee_save_regs[] = {
#if TCG_TARGET_REG_BITS == 64
    TCG_REG_RBP,
    TCG_REG_RBX,
#if defined(_WIN64)
    TCG_REG_RDI,
    TCG_REG_RSI,
#endif
    TCG_REG_R12,
    TCG_REG_R13,
    TCG_REG_R14, /* Currently used for the global env. */
    TCG_REG_R15,
#else
    TCG_REG_EBP, /* Currently used for the global env. */
    TCG_REG_EBX,
    TCG_REG_ESI,
    TCG_REG_EDI,
#endif
};

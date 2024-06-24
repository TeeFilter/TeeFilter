/*
 * Copyright (c) 2013-2019, ARM Limited and Contributors. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <assert.h>
#include <string.h>

#include <common/debug.h>
#include <common/runtime_svc.h>
#include <drivers/console.h>
#include <context.h>

extern void store_current_gp_registers(struct gp_regs* regs);
extern void store_current_el3_registers(struct el3_state* state);

void current_register_dump() {
  struct gp_regs gpregs;
  store_current_gp_registers(&gpregs);

  uint64_t x0 = read_ctx_reg(&gpregs, CTX_GPREG_X0);
  uint64_t x1 = read_ctx_reg(&gpregs, CTX_GPREG_X1);
  uint64_t x2 = read_ctx_reg(&gpregs, CTX_GPREG_X2);
  uint64_t x3 = read_ctx_reg(&gpregs, CTX_GPREG_X3);
  uint64_t x4 = read_ctx_reg(&gpregs, CTX_GPREG_X4);
  uint64_t x5 = read_ctx_reg(&gpregs, CTX_GPREG_X5);
  uint64_t x6 = read_ctx_reg(&gpregs, CTX_GPREG_X6);
  uint64_t x7 = read_ctx_reg(&gpregs, CTX_GPREG_X7);
  uint64_t x8 = read_ctx_reg(&gpregs, CTX_GPREG_X8);
  uint64_t x9 = read_ctx_reg(&gpregs, CTX_GPREG_X9);

  uint64_t x10 = read_ctx_reg(&gpregs, CTX_GPREG_X10);
  uint64_t x11 = read_ctx_reg(&gpregs, CTX_GPREG_X11);
  uint64_t x12 = read_ctx_reg(&gpregs, CTX_GPREG_X12);
  uint64_t x13 = read_ctx_reg(&gpregs, CTX_GPREG_X13);
  uint64_t x14 = read_ctx_reg(&gpregs, CTX_GPREG_X14);
  uint64_t x15 = read_ctx_reg(&gpregs, CTX_GPREG_X15);
  uint64_t x16 = read_ctx_reg(&gpregs, CTX_GPREG_X16);
  uint64_t x17 = read_ctx_reg(&gpregs, CTX_GPREG_X17);
  uint64_t x18 = read_ctx_reg(&gpregs, CTX_GPREG_X18);
  uint64_t x19 = read_ctx_reg(&gpregs, CTX_GPREG_X19);

  uint64_t x20 = read_ctx_reg(&gpregs, CTX_GPREG_X20);
  uint64_t x21 = read_ctx_reg(&gpregs, CTX_GPREG_X21);
  uint64_t x22 = read_ctx_reg(&gpregs, CTX_GPREG_X22);
  uint64_t x23 = read_ctx_reg(&gpregs, CTX_GPREG_X23);
  uint64_t x24 = read_ctx_reg(&gpregs, CTX_GPREG_X24);
  uint64_t x25 = read_ctx_reg(&gpregs, CTX_GPREG_X25);
  uint64_t x26 = read_ctx_reg(&gpregs, CTX_GPREG_X26);
  uint64_t x27 = read_ctx_reg(&gpregs, CTX_GPREG_X27);
  uint64_t x28 = read_ctx_reg(&gpregs, CTX_GPREG_X28);
  uint64_t x29 = read_ctx_reg(&gpregs, CTX_GPREG_X29);

  uint64_t lr = read_ctx_reg(&gpregs, CTX_GPREG_LR);
  uint64_t sp_el0 = read_ctx_reg(&gpregs, CTX_GPREG_SP_EL0);

  INFO("GP Register Dump\n");
  INFO(" x0: 0x%016llx   x1:  0x%016llx    x2: 0x%016llx\n", x0, x1, x2);
  INFO(" x3: 0x%016llx   x4:  0x%016llx    x5: 0x%016llx\n", x3, x4, x5);
  INFO(" x6: 0x%016llx   x7:  0x%016llx    x8: 0x%016llx\n", x6, x7, x8);
  INFO(" x9: 0x%016llx   x10: 0x%016llx   x11: 0x%016llx\n", x9, x10, x11);
  INFO("x12: 0x%016llx   x13: 0x%016llx   x14: 0x%016llx\n", x12, x13, x14);
  INFO("x15: 0x%016llx   x16: 0x%016llx   x17: 0x%016llx\n", x15, x16, x17);
  INFO("x18: 0x%016llx   x19: 0x%016llx   x20: 0x%016llx\n", x18, x19, x20);
  INFO("x21: 0x%016llx   x22: 0x%016llx   x23: 0x%016llx\n", x21, x22, x23);
  INFO("x24: 0x%016llx   x25: 0x%016llx   x26: 0x%016llx\n", x24, x25, x26);
  INFO("x27: 0x%016llx   x28: 0x%016llx   x29: 0x%016llx\n", x27, x28, x29);
  INFO("LR:  0x%016llx   SP_EL0: 0x%016llx\n", lr, sp_el0);

  struct el3_state el3regs;
  // The interrupt routine only partially saves context information to the
  // following struct so far:
  store_current_el3_registers(&el3regs);

  INFO("EL3 State Register Dump\n");
  uint64_t scr_el3 = read_ctx_reg(&el3regs, CTX_SCR_EL3);
  uint64_t spsr_el3 = read_ctx_reg(&el3regs, CTX_SPSR_EL3);
  uint64_t elr_el3 = read_ctx_reg(&el3regs, CTX_ELR_EL3);
  uint64_t esr_el3 = read_ctx_reg(&el3regs, CTX_ESR_EL3);

  INFO("SCR_EL3:  0x%016llx   SPSR_EL3: 0x%016llx\n", scr_el3, spsr_el3);
  INFO("ELR_EL3:  0x%016llx   ESR_EL3: 0x%016llx\n", elr_el3, esr_el3);
}

void my_report_unhandled_exception() {
   INFO("We are in my_report_unhandled_exception\n");
   current_register_dump();
}

void my_report_unhandled_interrupt() {
   INFO("We are in my_report_unhandled_interrupt\n");
   current_register_dump();
}

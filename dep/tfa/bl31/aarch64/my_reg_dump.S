/*
 * Copyright (c) 2018-2019, ARM Limited and Contributors. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <context.h>
#include <asm_macros.S>
#include <cpu_macros.S>

	.globl	store_current_gp_registers
  .globl  store_current_el3_registers


/*
 * Function to store the current registers to the struct gp_regs pointer
 * that is provided as the first argument.
 */
func store_current_gp_registers
	stp	x0, x1, [x0, CTX_GPREG_X0]
	stp	x2, x3, [x0, CTX_GPREG_X2]
	stp	x4, x5, [x0, CTX_GPREG_X4]
	stp	x6, x7, [x0, CTX_GPREG_X6]
	stp	x8, x9, [x0, CTX_GPREG_X8]
	stp	x10, x11, [x0, CTX_GPREG_X10]
	stp	x12, x13, [x0, CTX_GPREG_X12]
	stp	x14, x15, [x0, CTX_GPREG_X14]
	stp	x16, x17, [x0, CTX_GPREG_X16]
	stp	x18, x19, [x0, CTX_GPREG_X18]
	stp	x20, x21, [x0, CTX_GPREG_X20]
	stp	x22, x23, [x0, CTX_GPREG_X22]
	stp	x24, x25, [x0, CTX_GPREG_X24]
	stp	x26, x27, [x0, CTX_GPREG_X26]
	stp	x28, x29, [x0, CTX_GPREG_X28]
  ret
endfunc store_current_gp_registers


/*
 * Function to store the current registers to the struct el3_state pointer
 * that is provided as the first argument.
 */
func store_current_el3_registers
  mrs	x1, scr_el3
	mrs	x2, esr_el3
	stp	x1, x2, [x0, #CTX_SCR_EL3]

  mrs	x1, spsr_el3
	mrs	x2, elr_el3
	stp	x1, x2, [x0, #CTX_SPSR_EL3]

  ret
endfunc store_current_el3_registers

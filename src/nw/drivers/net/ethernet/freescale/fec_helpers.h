/*******************************************************************************
* Copyright (C) 2022-2024 Jonas Röckl <joroec@gmx.net>
* This program is free software; you can redistribute it and/or
* modify it under the terms of the GNU General Public License
* as published by the Free Software Foundation; either version 2
* of the License, or (at your option) any later version.
*
* This program is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
* GNU General Public License for more details.
*
* You should have received a copy of the GNU General Public License
* along with this program; If not, see <http://www.gnu.org/licenses/>.
*******************************************************************************/

#ifndef FEC_HELPERS_H
#define	FEC_HELPERS_H

#include <linux/arm-smccc.h>

# define TRAP_TO_EL3


// ----------------------------------------------------------------------------
// Address translation helpers
// ----------------------------------------------------------------------------

#ifdef TRAP_TO_EL3

#define MASK_47_TO_12 0x0000FFFFFFFFF000ULL
#define MASK_11_TO_0  0x0000000000000FFFULL

/* This function maps a NW virtual address to a physical address */
__attribute__((always_inline))
static inline u64 translate_el1(u64 virt_addr) {
	u64 phys_addr = virt_addr;
	asm("AT S1E1R, %[a];"
		"MRS %[a], PAR_EL1;"
		:[a] "+r" (phys_addr));

	if((1 & phys_addr)) {
    // translation failed bit
		printk(KERN_ALERT "EL1 translation fault %llx for addr 0x%llx\n", phys_addr,
      virt_addr);
		return phys_addr;
	}

	phys_addr = (MASK_47_TO_12 & phys_addr) + (MASK_11_TO_0 & virt_addr);
	return phys_addr;
}

#endif

// ----------------------------------------------------------------------------
// The following routines are made for trapping and emulating access to
// protected device peripheral MMIO-mapped memory.
// ----------------------------------------------------------------------------

#ifdef TRAP_TO_EL3

#define FUNCID_OEN_SHIFT		UL(24)
#define FUNCID_OEN_MASK			UL(0x3f)
#define FUNCID_OEN_WIDTH		UL(6)

#define SMC_TYPE_FAST			UL(1)
#define SMC_TYPE_YIELD			UL(0)

#define FUNCID_TYPE_SHIFT		UL(31)
#define FUNCID_TYPE_MASK		UL(0x1)
#define FUNCID_TYPE_WIDTH		UL(1)

#define FUNCID_TYPE (SMC_TYPE_FAST << FUNCID_TYPE_SHIFT)

#define FUNCID_PROT_NIC_RAW UL(19)
#define FUNCID_PROT_NIC_OEN (FUNCID_PROT_NIC_RAW << FUNCID_OEN_SHIFT)
#define FUNCID_PROT_NIC (FUNCID_PROT_NIC_OEN | FUNCID_TYPE)

#define FUNCID_WRITE_32_RAW UL(20)
#define FUNCID_WRITE_32_OEN (FUNCID_WRITE_32_RAW << FUNCID_OEN_SHIFT)
#define FUNCID_WRITE_32 (FUNCID_WRITE_32_OEN | FUNCID_TYPE)

#define FUNCID_READ_32_RAW UL(21)
#define FUNCID_READ_32_OEN (FUNCID_READ_32_RAW << FUNCID_OEN_SHIFT)
#define FUNCID_READ_32 (FUNCID_READ_32_OEN | FUNCID_TYPE)


#define FUNCID_TX_TOS_RAW UL(22)
#define FUNCID_TX_TOS_OEN (FUNCID_TX_TOS_RAW << FUNCID_OEN_SHIFT)
#define FUNCID_TX_TOS (FUNCID_TX_TOS_OEN | FUNCID_TYPE)

#define FUNCID_TX_FRS_RAW UL(23)
#define FUNCID_TX_FRS_OEN (FUNCID_TX_FRS_RAW << FUNCID_OEN_SHIFT)
#define FUNCID_TX_FRS (FUNCID_TX_FRS_OEN | FUNCID_TYPE)

#define FUNCID_RX_FRS_RAW UL(24)
#define FUNCID_RX_FRS_OEN (FUNCID_RX_FRS_RAW << FUNCID_OEN_SHIFT)
#define FUNCID_RX_FRS (FUNCID_RX_FRS_OEN | FUNCID_TYPE)

#define FUNCID_RX_TOS_RAW UL(25)
#define FUNCID_RX_TOS_OEN (FUNCID_RX_TOS_RAW << FUNCID_OEN_SHIFT)
#define FUNCID_RX_TOS (FUNCID_RX_TOS_OEN | FUNCID_TYPE)


__attribute__((always_inline))
static inline void prot_nic(void) {
	struct arm_smccc_res res;

	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);

	arm_smccc_smc(
		FUNCID_PROT_NIC, // a0
		0, // a1
		0, // a2
		0, // a3
		0, // a4
		0, // a5
		0, // a6
		0, // a7
		&res // res
	);

	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
}


__attribute__((always_inline))
static inline void tx_tos(int queue, unsigned int index) {
	struct arm_smccc_res res;
	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
	arm_smccc_smc(
		FUNCID_TX_TOS, // a0
		(uint64_t) queue, // a1
		(uint64_t) index, // a2
		0, // a3
		0, // a4
		0, // a5
		0, // a6
		0, // a7
		&res // res
	);
	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
}

__attribute__((always_inline))
static inline void tx_frs(int queue, unsigned int pending) {
	struct arm_smccc_res res;
	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
	arm_smccc_smc(
		FUNCID_TX_FRS, // a0
		(uint64_t) queue, // a1
		(uint64_t) pending, // a2
		0, // a3
		0, // a4
		0, // a5
		0, // a6
		0, // a7
		&res // res
	);
	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
}

__attribute__((always_inline))
static inline void rx_frs(int queue, unsigned int index, unsigned int budget) {
	struct arm_smccc_res res;
	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
	arm_smccc_smc(
		FUNCID_RX_FRS, // a0
		(uint64_t) queue, // a1
		(uint64_t) index, // a2
		(uint64_t) budget, // a3
		0, // a4
		0, // a5
		0, // a6
		0, // a7
		&res // res
	);
	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
}

__attribute__((always_inline))
static inline void rx_tos(int queue, unsigned int index, unsigned int received) {
	struct arm_smccc_res res;
	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
	arm_smccc_smc(
		FUNCID_RX_TOS, // a0
		(uint64_t) queue, // a1
		(uint64_t) index, // a2
		(uint64_t) received, // a3
		0, // a4
		0, // a5
		0, // a6
		0, // a7
		&res // res
	);
	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
}

__attribute__((always_inline))
static inline void my_writel(u32 value, volatile void __iomem *address) {
	struct arm_smccc_res res;
  u64 val, adr;

	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);

  val = (u64) value;
  adr = translate_el1((u64) address);

	arm_smccc_smc(
		FUNCID_WRITE_32, // a0
		value, // a1
		adr, // a2
		0, // a3
		0, // a4
		0, // a5
		0, // a6
		0, // a7
		&res // res
	);

	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
}

__attribute__((always_inline))
static inline u32 my_readl(volatile void __iomem *address) {
	struct arm_smccc_res res;
  u64 adr;

	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);

  adr = translate_el1((u64) address);

	arm_smccc_smc(
		FUNCID_READ_32, // a0
		adr, // a1
		0, // a2
		0, // a3
		0, // a4
		0, // a5
		0, // a6
		0, // a7
		&res // res
	);

	// printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);

  return (u32) res.a0;
}


#endif

// ----------------------------------------------------------------------------
// For reasons of debugging
// ----------------------------------------------------------------------------

#ifndef TRAP_TO_EL3

__attribute__((always_inline))
static inline void my_writel(u32 value, volatile void __iomem *address) {
  writel(value, address);
}

__attribute__((always_inline))
static inline u32 my_readl(volatile void __iomem *address) {
  return readl(address);
}

#endif

#endif /* FEC_HELPERS_H */

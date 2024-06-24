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

#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>

#include <linux/arm-smccc.h>

#include "certrbpf_program.h"

#include "hacl/Hacl_Ed25519.h"

// ----------------------------------------------------------------------------
// Address translation helpers
// ----------------------------------------------------------------------------

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

/* -----------------------------------------------------------------------------
* KEY MATERIAL
* --------------------------------------------------------------------------- */

// BASE64: RQwD+n5Uv6NqfFTTiBTvX5w/vsLNa5IQGvGe260/VAc=
/* static uint8_t ed25519_hub_public_key[] = {
  0x45, 0x0c, 0x03, 0xfa, 0x7e, 0x54, 0xbf, 0xa3, 0x6a, 0x7c, 0x54, 0xd3,
  0x88, 0x14, 0xef, 0x5f, 0x9c, 0x3f, 0xbe, 0xc2, 0xcd, 0x6b, 0x92, 0x10,
  0x1a, 0xf1, 0x9e, 0xdb, 0xad, 0x3f, 0x54, 0x07
}; */

// BASE64: hGCbtob+DIWX9drlVTMVwsVukn8dvs2TcIWFgZg6yCY=
static uint8_t ed25519_hub_private_key[] = {
  0x84, 0x60, 0x9b, 0xb6, 0x86, 0xfe, 0x0c, 0x85, 0x97, 0xf5, 0xda, 0xe5,
  0x55, 0x33, 0x15, 0xc2, 0xc5, 0x6e, 0x92, 0x7f, 0x1d, 0xbe, 0xcd, 0x93,
  0x70, 0x85, 0x85, 0x81, 0x98, 0x3a, 0xc8, 0x26
};

// ----------------------------------------------------------------------------
// Message Definitions
// ----------------------------------------------------------------------------

typedef uint32_t MSG_Opcode;

#define MSG_UPDATE_SUBMIT 10

#define RULE_SIZE 1024

struct Update {
  MSG_Opcode  opcode;
  uint64_t nonce;
  uint32_t length;
  uint8_t rule[RULE_SIZE];
	uint8_t     signature[64];
} __attribute__((packed, aligned(4)));

#define SIGNED_SIZE  sizeof(MSG_Opcode) + sizeof(uint64_t) + sizeof(uint32_t) + 1024 * sizeof(uint8_t)

// ----------------------------------------------------------------------------
// SMC Protocol Definition
// ----------------------------------------------------------------------------

#define FUNCID_OEN_SHIFT		UL(24)
#define FUNCID_OEN_MASK			UL(0x3f)
#define FUNCID_OEN_WIDTH		UL(6)

#define SMC_TYPE_FAST			UL(1)
#define SMC_TYPE_YIELD			UL(0)

#define FUNCID_TYPE_SHIFT		UL(31)
#define FUNCID_TYPE_MASK		UL(0x1)
#define FUNCID_TYPE_WIDTH		UL(1)

#define FUNCID_TYPE (SMC_TYPE_FAST << FUNCID_TYPE_SHIFT)

#define FUNCID_UPDATE_NONCE_RAW UL(26)
#define FUNCID_UPDATE_NONCE_OEN (FUNCID_UPDATE_NONCE_RAW << FUNCID_OEN_SHIFT)
#define FUNCID_UPDATE_NONCE (FUNCID_UPDATE_NONCE_OEN | FUNCID_TYPE)

#define FUNCID_UPDATE_SUBMIT_RAW UL(27)
#define FUNCID_UPDATE_SUBMIT_OEN (FUNCID_UPDATE_SUBMIT_RAW << FUNCID_OEN_SHIFT)
#define FUNCID_UPDATE_SUBMIT (FUNCID_UPDATE_SUBMIT_OEN | FUNCID_TYPE)

// ----------------------------------------------------------------------------
// SMC Wrappers
// ----------------------------------------------------------------------------

__attribute__((always_inline))
static inline uint64_t updater_nonce(void) {
	struct arm_smccc_res res;
	printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
	arm_smccc_smc(
		FUNCID_UPDATE_NONCE, // a0
		0, // a1
		0, // a2
		0, // a3
		0, // a4
		0, // a5
		0, // a6
		0, // a7
		&res // res
	);
	printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
  return res.a0;
}

__attribute__((always_inline))
static inline bool updater_submit(struct Update* update) {
	struct arm_smccc_res res;
	printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
	arm_smccc_smc(
		FUNCID_UPDATE_SUBMIT, // a0
		translate_el1((uint64_t) update), // a1
		0, // a2
		0, // a3
		0, // a4
		0, // a5
		0, // a6
		0, // a7
		&res // res
	);
	printk(KERN_ALERT "DEBUG: Passed %s %d \n",__FUNCTION__,__LINE__);
  return res.a0;
}

// ----------------------------------------------------------------------------
// Global variables
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
// Init Function of the LKM (Constructor)
// ----------------------------------------------------------------------------

static int updater_init(void) {
    printk(KERN_DEBUG "Initializing LKM\n");

    printk(KERN_DEBUG "Retrieve nonce\n");
    uint64_t nonce = updater_nonce();
    printk(KERN_DEBUG "Nonce: %llx\n", nonce);

    printk(KERN_DEBUG "Build update\n");
    struct Update update;
    update.opcode = MSG_UPDATE_SUBMIT;
    update.nonce = nonce;
    update.length = bpf_program_len;

    memset(update.rule, 0x0, RULE_SIZE);
    memcpy(update.rule, bpf_program, bpf_program_len);

    // Sign the update (normally done at the remote party)
    printk(KERN_DEBUG "Sign the update\n");
    Hacl_Ed25519_sign((uint8_t*) &update.signature, ed25519_hub_private_key,
      SIGNED_SIZE, (uint8_t*) &update);
    printk(KERN_DEBUG "Done signing the update\n");

    updater_submit(&update);

    printk(KERN_DEBUG "Done loading LKM\n");
    return 0;
}

// ----------------------------------------------------------------------------
// Exit Function of the LKM (Destructor)
// ----------------------------------------------------------------------------

static void updater_exit(void) {
    printk(KERN_DEBUG "Removing Module\n");
}

// ----------------------------------------------------------------------------
// Meta Information for the module
// ----------------------------------------------------------------------------

module_init(updater_init);
module_exit(updater_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Jonas Röckl <joroec@gmx.net>");
MODULE_DESCRIPTION("TeeFilter Rule Updater");

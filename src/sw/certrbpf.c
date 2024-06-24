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

#include "certrbpf.h"

#include <string.h>
#include <common/debug.h>

#include "certrbpf_interpreter.h"
#include "certrbpf_verifier.h"
#include "certrbpf_program.h"

/* -----------------------------------------------------------------------------
* Public Interface Declaration
* --------------------------------------------------------------------------- */

void certrbpf_init(struct bpf* bpf) {
  INFO("Initializing CertrBPF interpreter\n");

  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(bpf), "certrbpf_update #1");
  #endif

  // initialize packet memory region
  // the addresses are just placeholders for now since we don't know
  // where the packet will be placed in memory
  bpf->regions[0].start_addr = BPF_PACKET_ADDR;
  bpf->regions[0].block_size = 0;
  bpf->regions[0].block_perm = Readable;
  bpf->regions[0].block_ptr  = 0;

  // initialize stack memory region
  bpf->regions[1].start_addr = BPF_STACK_ADDR;
  bpf->regions[1].block_size = sizeof(bpf->stack)+1;
  bpf->regions[1].block_perm = Writable;
  bpf->regions[1].block_ptr  = bpf->stack;

  // initialize interpreter bpf_state
  bpf->bpf_state.state_pc = 0;
  bpf->bpf_state.bpf_flag = vBPF_OK;
  memset(bpf->bpf_state.regsmap, 0, sizeof(bpf->bpf_state.regsmap));
  bpf->bpf_state.mrs_num  = 2;
  bpf->bpf_state.mrs      = bpf->regions;

  if(bpf->dynamic_rule_enabled) {
    bpf->bpf_state.ins_len  = bpf->dynamic_rule_length/8;
    bpf->bpf_state.ins      = (uint64_t *) bpf->dynamic_rule;
  } else {
    bpf->bpf_state.ins_len  = bpf_program_len/8;
    bpf->bpf_state.ins      = (uint64_t *) bpf_program;
  }

  struct verifier_state vf_state =  {
    .ins_len  = bpf->bpf_state.ins_len,
    .ins      = bpf->bpf_state.ins,
  };

  #ifndef MODEL
  // run the verifier
  if (!bpf_verifier(&vf_state)) {
    ERROR("bpf_verifier failed!\n");
    bpf->initialized = false;
    return;
  }
  #endif

  bpf->initialized = true;
}


bool certrbpf_run(struct bpf* bpf, uint8_t* packet, size_t packet_len,
    uint32_t direction) {
  if(!bpf->initialized){
    certrbpf_init(bpf);
  }

  // reset and initialize the bpf_state
  bpf->bpf_state.state_pc = 0;
  bpf->bpf_state.bpf_flag = vBPF_OK;
  memset(bpf->bpf_state.regsmap, 0, sizeof(bpf->bpf_state.regsmap));
  bpf->bpf_state.regsmap[1] = BPF_PACKET_ADDR;
  bpf->bpf_state.regsmap[2] = packet_len;
  bpf->bpf_state.regsmap[3] = direction;
  bpf->bpf_state.regsmap[10] = BPF_STACK_ADDR + sizeof(bpf->stack);

  // update the packet memory region
  bpf->regions[0].block_size = packet_len+1;
  bpf->regions[0].block_ptr = packet;

  bpf->bpf_state.mrs_num = 2;
  bpf->bpf_state.mrs = bpf->regions;

  uint64_t res;
  // Verify with CBMC that bpf_state and memory regions suffice pre-conditions.
  // Then, we know for sure that the call to bpf_interpreter is memory-safe
  // since the interpreter has been formally verified with Coq (see paper).
	#ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(bpf), "certrbpf #1");

	__CPROVER_assert(sizeof(bpf->regions) / sizeof(struct memory_region ) == 2, "more than two regions");

	__CPROVER_assert(bpf->regions[0].start_addr == BPF_PACKET_ADDR, "region 0 invalid");
	__CPROVER_assert(bpf->regions[0].block_size == packet_len+1, "region 0 invalid");
	__CPROVER_assert(bpf->regions[0].block_ptr == packet, "region 0 invalid");

	__CPROVER_assert(bpf->regions[1].start_addr == BPF_STACK_ADDR, "region 1 invalid");
	__CPROVER_assert(bpf->regions[1].block_size == sizeof(bpf->stack)+1, "region 1 invalid");
	__CPROVER_assert(bpf->regions[1].block_ptr == bpf->stack, "region 1 invalid");

	__CPROVER_assert(bpf->bpf_state.mrs_num == 2, "more than two regions");
	__CPROVER_assert(bpf->bpf_state.mrs == bpf->regions, "more than two regions");

	__CPROVER_assert(bpf->initialized, "rBPF not initialized or verified");

  {
    #ifdef MODEL_ASSUME_POSITIVE_VERDICT
    res = 0x1;
    #else
    res = 0x0;
    #endif
  }

	#endif

  /* Call the interpreter.
  * If the interpreter does not return successfully (e.g., cause the filter code
  * emitted an illegal memory access instruction), we do not allow the packet.
  * Thus, we do not need to include boundary checks in the filter code since we
  * know the code is interpreted. We also check the regular return value if the
  * code executed directly to determine whether the packet is allowed.
  */
  #ifndef MODEL
  res = bpf_interpreter(&bpf->bpf_state, BPF_FUEL);
  if(bpf->bpf_state.bpf_flag != vBPF_SUCC_RETURN) {
    ERROR("certrbpf_run failed: %d\n", bpf->bpf_state.bpf_flag);
    return false;
  }
  #endif

  bool verdict = res == 1;
  return verdict;
}


void certrbpf_update(struct bpf* bpf, uint8_t* rule, uint32_t length) {
  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(bpf), "certrbpf_update #1");
  #endif

  memcpy(bpf->dynamic_rule, rule, BPF_DYNAMIC_RULE_SIZE);
  bpf->dynamic_rule_length = length;
  bpf->dynamic_rule_enabled = true;
  bpf->initialized = false;
}

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

#include <stdint.h>
#include <lib/mmio.h>
#include <endian.h>
#include <arch_helpers.h>
#include <platform_def.h>

#include "teefilter_rx_frs.h"
#include "teefilter_rx_common.h"
#include "teefilter_common.h"
#include "certrbpf.h"
#include "plat/memcpy.h"
#include "plat/memset.h"
#include "checks.h"
#include "descring.h"
#include "dataring.h"
#include "state.h"

/* -----------------------------------------------------------------------------
* RX_FRS
* --------------------------------------------------------------------------- */

/*
* - is not based on any sort of global state
* - does not exhibit indeterministic behavior
* - dstData is required to point to a FEC_MAX_FRAME_LEN buffer
* - originData is required to be a buffer of length originSize
* - originSize is required to be valid. Caller needs to ensure that!
* - bpf is required to be initialized. ATF guarantees that.
*/
void rx_frs_frame_handler(uint8_t* dstData, uint8_t* originData,
    uint16_t originSize, struct bpf* bpf) {

  // In the model, we do not differentiate between NW and SW memory.
  // We verify that "is_nw_ram_region" is correct in a seperate proof.
  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(dstData, FEC_MAX_FRAME_LEN), "rx_frs_frame_handler #1");
  __CPROVER_assert(__CPROVER_rw_ok(bpf), "rx_frs_frame_handler #2");
  #else
  if(!is_nw_ram_region((uint64_t) dstData, FEC_MAX_FRAME_LEN)) {
    ERROR("frame_handler: Not a NW RAM region: %p, %d\n", dstData, originSize);
    return;
  }
  #endif

  // We need to read the actual packet. We do this BEFORE the filtering so
  // that the filter is able to access the actual new packet's date (e.g.,
  // the packets header).
  // In the model, we do not include caching operations as they are implemented
  // in assembly, which we cannot verif with CBMC.
  #ifndef MODEL
  inv_dcache_range((uint64_t) originData, originSize);
  #endif

  // Run the interpreter with the packet to get the verdict
  // NOTE: packet contains 2 bytes of padding before the ethernet header
  // this is automatically added by the NIC on RX (if ENETn_RACC[SHIFT16] is set)
  // and by the dataring implementation on TX
  bool verdict = certrbpf_run(bpf, originData, originSize, DIRECTION_INBOUND);
  if(!verdict) {
    // inject empty error frame
    destroy(dstData, FEC_MAX_FRAME_LEN);
    return;
  }

  // Copy the legit packet to NW.
  // In the model, we use regular variants of the memory primitives.
  // On real hardware, we use optimized veriants based on assembly. Thus, we
  // cannot verify them with CBMC. They are directly provided by ARM. We assume
  // that they are correct.
  #ifdef MODEL
  memcpy(dstData, originData, originSize);
  #else
  memcpy_aarch64(dstData, originData, originSize);
  #endif

  dsb();
}


/*
* - is not based on any sort of global state
* - does not exhibit indeterministic behavior
* - dest is required to be a valid pointer! Caller needs to ensure that!
* - origin is required to be a valid pointer! Caller needs to ensure that!
* - index needs to be valid! Caller needs to ensure that!
* - element needs to be a valid pointer! Caller needs to ensure that!
* - bpf is required to be initialized. ATF guarantees that.
*/
void rx_frs_bd_handler(struct bufdesc_ex* dest, struct bufdesc_ex* origin,
    uint32_t index, struct element* element, struct bpf* bpf) {

  // We do not include endianess in the model
  #ifdef MODEL
  uint8_t* originData = origin->desc.cbd_bufaddr;
	uint16_t originSize = origin->desc.cbd_datlen;
  uint32_t dstData = dest->desc.cbd_bufaddr;
	uint16_t status = origin->desc.cbd_sc;
  #else
  uint32_t originData = le32toh(origin->desc.cbd_bufaddr);
	uint16_t originSize = le16toh(origin->desc.cbd_datlen);
  uint32_t dstData = le32toh(dest->desc.cbd_bufaddr);
	uint16_t status = le16toh(origin->desc.cbd_sc);
  #endif

  // Check source frame for validity and correct length.
  // Those are the preconditions for the frame_handler.
  if((uint8_t*) ((uint64_t) originData) != ((uint8_t*) element)) {
    ERROR("bd_handler: Not a shadow ring region: %llx\n", (uint64_t) originData);
    return;
  }

  if(!check_rx_packet_size(originSize)) {
    ERROR("bd_handler: Not a valid length: %x\n", originSize);
    return;
  }

  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(originData, originSize), "rx_frs_bd_handler #1");
  __CPROVER_assert(__CPROVER_rw_ok(bpf), "rx_frs_bd_handler #2");
  #else
	rx_frs_frame_handler(
    (uint8_t*)((uint64_t) dstData),
    (uint8_t*) ((uint64_t) originData),
    originSize,
    bpf
    );
  #endif

  // Verify that BD wraps are correctly handled
  if(index == DESCRING_ELEMENTS_N - 1 && (status & BD_SC_WRAP) == 0x0) {
    ERROR("rx_frs3: Last descriptor does not WRAP\n");
    origin->desc.cbd_sc = status | BD_SC_WRAP;
  }

  // After the data, we can copy over the descriptor, issuing the NW address
  // as a new address for the buffer descriptor.
  copy_desc(dest, origin, dstData);
}


/*
* - is not based on any sort of global state (except the sync variable for the model)
* - does not exhibit indeterministic behavior
* - current needs to be valid! Caller needs to ensure that!
* - budget needs to be valid! Caller needs to ensure that!
* - nw_ring needs to be a valid pointer. Caller needs to ensure that!
* - shadow_ring needs to be a valid pointer. Caller needs to ensure that!
* - shadow_data needs to be a valid pointer. Caller needs to ensure that!
* - bpf is required to be initialized. ATF guarantees that.
*/
void rx_frs_iterator(uint32_t current, uint32_t budget, struct descring* nw_ring,
    struct descring* shadow_ring, struct dataring* shadow_data, struct bpf* bpf) {

  for(uint32_t i=0; i<budget; i++) {
    uint32_t index = (current + i) % DESCRING_ELEMENTS_N;
    // We know that index is valid, i.e., in [0, DESCRING_ELEMENTS_N-1] here

  	struct bufdesc_ex* origin = &shadow_ring->elements[index];

    // We do not include endianess in our proof since it influences its duration
    // exponentially and prevents that we can reason with higher data types.
    #ifdef MODEL
    uint16_t status = origin->desc.cbd_sc;
    #else
    uint16_t status = le16toh(origin->desc.cbd_sc);
    #endif

    // We overapproximate the solution in our model. If we would allow shortcuts,
    // the number of potential paths through the function explosed. An
    // overapproximation does not harm the validity of the proof.
    #ifndef MODEL_SKIP_SHORTCUT
    if(status & BD_ENET_RX_EMPTY) {
      break;
    }
    #endif

    struct bufdesc_ex* dest = &nw_ring->elements[index];
    struct element* element = &shadow_data->elements[index];

    #ifdef MODEL
    __CPROVER_assert(__CPROVER_rw_ok(dest), "rx_frs_iterator #1");
    __CPROVER_assert(__CPROVER_rw_ok(origin), "rx_frs_iterator #2");
    __CPROVER_assert(check_pos(index), "rx_frs_iterator #3");
    __CPROVER_assert(__CPROVER_rw_ok(element), "rx_frs_iterator #4");
    __CPROVER_assert(__CPROVER_rw_ok(bpf), "rx_frs_iterator #5");
    // To model that we called rx_frs_bd_handler for a certain index, we set
    // the sync variable. It is defined in the harness.
    extern bool sync[DESCRING_ELEMENTS_N];
    sync[index] = true;
    #else
    rx_frs_bd_handler(dest, origin, index, element, bpf);
    #endif
  }
}


/*
* - does access global state before calling dependent functions.
* - state needs to be initialized. ATF guarantees that.
* - Variables in state are only read but never written in this function. Thus,
*   there are no side effects on the global "state" object.
* - does not exhibit indeterministic behavior
* - queue, current, and bugdet can have arbitrary values
* - bpf is required to be initialized. ATF guarantees that.
*/
void rx_frs(uint32_t queue, uint32_t current, uint32_t budget) {
  if(!check_rx_queue(queue)) {
    ERROR("Invalid RX queue: %d\n", queue);
    return;
  }

  if(!check_pos(current)) {
    ERROR("Invalid current: %d\n", current);
    return;
  }

  if(!check_budget(budget)) {
    ERROR("Invalid budget: %d\n", budget);
    return;
  }

  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(state.nw_rx_descrings[queue]), "rx_frs #0");
  #else
  if(!is_nw_ram_region((uint64_t) state.nw_rx_descrings[queue], DESCRING_SIZE_BYTES)) {
    ERROR("NW ring not correct: Not a NW RAM region: %llx, %d\n",
      (uint64_t) state.nw_rx_descrings[queue], DESCRING_SIZE_BYTES);
    return;
  }
  #endif
  struct descring* nw_ring = state.nw_rx_descrings[queue];

  struct descring* shadow_ring = state.shadow_rx_descrings[queue];
  if(!shadow_ring) {
    ERROR("Shadow ring is not initialized\n");
    return;
  }

  struct dataring* shadow_data = state.rx_datarings[queue];
  if(!shadow_data) {
    ERROR("Shadow data ring is not initialized\n");
    return;
  }

  struct bpf* bpf = &state.bpf;

  #ifdef MODEL
  __CPROVER_assert(check_pos(current), "rx_frs #1");
  __CPROVER_assert(check_budget(budget), "rx_frs #2");
  __CPROVER_assert(__CPROVER_rw_ok(nw_ring), "rx_frs #3");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_ring), "rx_frs #4");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_data), "rx_frs #5");
  __CPROVER_assert(__CPROVER_rw_ok(bpf), "rx_frs #6");
  #else
  rx_frs_iterator(current, budget, nw_ring, shadow_ring, shadow_data, bpf);
  #endif
}

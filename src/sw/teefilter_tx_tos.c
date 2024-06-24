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

#include "teefilter_tx_tos.h"
#include "teefilter_tx_common.h"
#include "teefilter_common.h"
#include "dataring.h"
#include "descring.h"
#include "certrbpf.h"
#include "plat/memcpy.h"
#include "checks.h"
#include "state.h"

/* -----------------------------------------------------------------------------
* TX_TOS
* --------------------------------------------------------------------------- */

/*
* - is not based on any sort of global state
* - does not exhibit indeterministic behavior
* - dstData is required to point to a SW_BUFFER_SIZE buffer. This is larger
*   than FEC_MAX_FRAME_LEN, which is important, since we need two additional
*   bytes so that the frame is aligned. We need an aligned packet so that the
*   eBPF interpreter can access the memory.
* - originData is required to be a buffer of length originSize
* - bpf is required to be initialized. ATF guarantees that.
*/
void tx_tos_frame_handler(uint8_t* dstData, uint8_t* originData, uint16_t originSize,
    struct bpf* bpf) {
  if(!check_tx_packet_size(originSize)) {
    ERROR("tx_handle_data: Illegal packet size: %d\n", originSize);
    destroy(dstData, DATARING_ELEMENT_SIZE_BYTES);
    return;
  }

  // In the model, we do not differentiate between NW and SW memory.
  // We verify that "is_nw_ram_region" is correct in a seperate proof.
  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(originData, originSize), "tx_tos_frame_handler #1");
  __CPROVER_assert(__CPROVER_rw_ok(bpf), "tx_tos_frame_handler #2");
  #else
  if(!is_nw_ram_region((uint64_t) originData, originSize)) {
    ERROR("frame_handler: Not a NW RAM region: %p, %d\n", originData, originSize);
    destroy(dstData, DATARING_ELEMENT_SIZE_BYTES);
    return;
  }
  #endif

  // Two bytes of padding are added before the packet to align the packet headers.
  // The eBPF code than accesses the memory in aligned mode, so we need to know
  // for sure that there are 2 bytes padding before the actual packet. We checked
  // this precondition in the calling function.
  #ifdef MODEL
  memcpy(dstData+2, originData, originSize); // size checked above
  #else
  memcpy_aarch64(dstData+2, originData, originSize); // size checked above
  #endif

	// We check the buffer descriptor and the data ring for validness and decide
	// on the packet (packet filtering)
  // Run the interpreter to check if the frame is legit
  bool verdict = certrbpf_run(bpf, dstData, originSize+2, DIRECTION_OUTBOUND);
  if(!verdict) {
    // inject empty frame
    destroy(dstData, DATARING_ELEMENT_SIZE_BYTES);
  }
}


/*
* - is not based on any sort of global state
* - does not exhibit indeterministic behavior
* - dest is required to be valid. Needs to be checked by caller!
* - origin is required to be valid. Needs to be checked by caller!
* - index is required to be valid. Needs to be checked by caller!
* - element is required to be valid. Needs to be checked by caller!
* - has_header is required to be valid. Needs to be checked by caller!
* - bpf is required to be initialized. ATF guarantees that.
*/
void tx_tos_bd_handler(struct bufdesc_ex* dest, struct bufdesc_ex* origin,
    uint32_t index, struct element* element, bool* has_header, struct bpf* bpf) {

	// Copy buffer descriptor to shadow ring to prevent concurrent updates while
	// we do our analysis: Important: Do NOT yet transmit ownership of the
  // descriptor to the NIC to prevent that the NIC transmits unchecked packages.
	uint16_t prev_status = copy_desc_wo_ownership(dest, origin);
  if(!(prev_status & BD_ENET_TX_READY)) {
    ERROR("tx_tos_bd_handler: BD not ready\n");
    return;
  }

  #ifdef MODEL
	uint64_t size = (uint64_t) dest->desc.cbd_datlen;
  uint8_t* origData = dest->desc.cbd_bufaddr;
	uint16_t status = dest->desc.cbd_sc;
  #else
	uint64_t size = (uint64_t) le16toh(dest->desc.cbd_datlen);
  uint8_t* origData = (uint8_t*) ((uint64_t) (le32toh(dest->desc.cbd_bufaddr)));
	uint16_t status = le16toh(dest->desc.cbd_sc);
  #endif

	// Check if we are about to put an BD to the BD ring that can contain a
	// header. If the packet could contain a header, we need to copy the data
	// (incl. the header) to the data ring.
	// If not, we currently refrain from copying the data.
	uint8_t* data = NULL;
	if(has_header[index]) {

    // We need at least two bytes of padding in the front
    if(DATARING_ELEMENT_SIZE_BYTES - 2 < size) {
      ERROR("tx_tos_bd_handler: No place for padding: %lld\n", size);
      return;
    }

    #ifdef MODEL
    __CPROVER_assert(__CPROVER_rw_ok(element), "tx_tos_bd_handler #1");
    __CPROVER_assert(DATARING_ELEMENT_SIZE_BYTES - 2 >= size, "tx_tos_bd_handler #2");
    __CPROVER_assert(__CPROVER_rw_ok(bpf), "tx_tos_bd_handler #3");
    #else
    tx_tos_frame_handler(element->data, origData, size, bpf);
    #endif

    // We need to remove the padding bytes here here because they should not be
    // send out or copied to the NW. This is possible because of the above
    // check.
  	data = element->data+2;
  } else {

    if(!check_tx_packet_size(size)) {
      ERROR("tx_tos_bd_handler: Illegal packet size: %lld\n", size);
      return;
    }

    // In the model, we do not differentiate between NW and SW memory.
    // We verify that "is_nw_ram_region" is correct in a seperate proof.
    #ifdef MODEL
    __CPROVER_assert(__CPROVER_rw_ok(origData, size), "tx_tos_bd_handler #4");
    #else
    if(!is_nw_ram_region((uint64_t) origData, size)) {
      ERROR("tx_tos_bd_handler: Not a NW RAM region: %p, %lld\n", origData, size);
      return;
    }
    #endif

    data = origData;
  }

	// Update the pointer to the data accordingly, depending on the data was
	// copied to the shadow buffer or not.
	update_data(dest, data);

  // sync to RAM, i.e. CLEAN, i.e. ensure that the data lands in RAM.
  // We need to do this AFTER the filtering so that the filter is able to
  // change the packet's data (e.g., the destination address).
  #ifndef MODEL
  clean_dcache_range((uint64_t) data, size);
  #endif

	// We look at the packet and set the information whether we need to filter
	// the next packet. We look at the dest buffer descriptor to prevent
	// TOCTOU race conditions.
	if(status & BD_ENET_TX_LAST) {
		has_header[(index+1) % DESCRING_ELEMENTS_N] = true;
	} else {
		has_header[(index+1) % DESCRING_ELEMENTS_N] = false;
	}

  // We need to enforce that WRAP is set if we are last in the ring.
  // Otherwise, a malicious NW might try to overrun the shadow ring buffers,
  // potentially causing harm.
  if(index == DESCRING_ELEMENTS_N - 1 && (status & BD_SC_WRAP) == 0x0) {
    ERROR("tx_tos3: Last descriptor does not WRAP\n");
    dest->desc.cbd_sc = status | BD_SC_WRAP;
  }

	// Transmit ownership
	transmit_ownership(dest);
}


/*
* We build chunks of 64 elements if there are many multiple frames for
* tranmission. We build two iterators. An upper layer that iterates over the
* chunks and a lower layer that iterates over the buffer descriptors.
* Then, we prove them individually. This way, we are able to verify them.
* Without that, we would end up in a state explosion.
* - is not based on any sort of global state (except the sync variable for the model)
* - does not exhibit indeterministic behavior
* - current needs to be valid! Caller needs to ensure that!
* - elements needs to be valid! Caller needs to ensure that!
* - nw_ring needs to be a valid pointer. Caller needs to ensure that!
* - shadow_ring needs to be a valid pointer. Caller needs to ensure that!
* - shadow_data needs to be a valid pointer. Caller needs to ensure that!
* - has_header is required to be valid. Needs to be checked by caller!
* - bpf is required to be initialized. ATF guarantees that.
*/
void tx_tos_iterator2(uint32_t current, uint32_t elements,
    struct descring* nw_ring, struct descring* shadow_ring,
    struct dataring* shadow_data, bool* has_header, struct bpf* bpf) {

  for(uint32_t i=0; i<elements; i++) {
    uint32_t index = (current + i) % DESCRING_ELEMENTS_N;
    // We know that index is valid, i.e., in [0, DESCRING_ELEMENTS_N-1] here

    struct bufdesc_ex* origin = &nw_ring->elements[index];

    #ifdef MODEL
    uint16_t status = origin->desc.cbd_sc;
    #else
    uint16_t status = le16toh(origin->desc.cbd_sc);
    #endif

    // We overapproximate the solution in our model. If we would allow shortcuts,
    // the number of potential paths through the function explosed. An
    // overapproximation does not harm the validity of the proof.
    #ifndef MODEL_SKIP_SHORTCUT
    if(!(status & BD_ENET_TX_READY)) {
      break;
    }
    #endif

    struct bufdesc_ex* dest = &shadow_ring->elements[index];
    struct element* element = &shadow_data->elements[index];

    #ifdef MODEL
    __CPROVER_assert(__CPROVER_rw_ok(dest), "tx_tos_iterator #1");
    __CPROVER_assert(__CPROVER_rw_ok(origin), "tx_tos_iterator #2");
    __CPROVER_assert(check_pos(index), "tx_tos_iterator #3");
    __CPROVER_assert(__CPROVER_rw_ok(element), "tx_tos_iterator #4");
    __CPROVER_assert(__CPROVER_rw_ok(has_header,
        DESCRING_ELEMENTS_N * sizeof(bool)), "tx_tos_iterator #5");
    __CPROVER_assert(__CPROVER_rw_ok(bpf), "tx_tos_iterator #6");
    // To model that we called tx_tos_bd_handler for a certain index, we set
    // the sync variable. It is defined in the harness.
    extern bool sync[DESCRING_ELEMENTS_N];
    sync[index] = true;
    #else
    tx_tos_bd_handler(dest, origin, index, element, has_header, bpf);
    #endif
  }
}


/*
* We build chunks of 64 elements if there are many multiple frames for
* tranmission. We build two iterators. An upper layer that iterates over the
* chunks and a lower layer that iterates over the buffer descriptors.
* Then, we prove them individually. This way, we are able to verify them.
* Without that, we would end up in a state explosion.
* - is not based on any sort of global state (except the sync variable for the model)
* - does not exhibit indeterministic behavior
* - current needs to be valid! Caller needs to ensure that!
* - shadow_tx_current needs to be valid! Caller needs to ensure that!
* - nw_ring needs to be a valid pointer. Caller needs to ensure that!
* - shadow_ring needs to be a valid pointer. Caller needs to ensure that!
* - shadow_data needs to be a valid pointer. Caller needs to ensure that!
* - has_header is required to be valid. Needs to be checked by caller!
* - bpf is required to be initialized. ATF guarantees that.
*/
void tx_tos_iterator(uint32_t current, uint32_t shadow_tx_current,
    struct descring* nw_ring, struct descring* shadow_ring,
    struct dataring* shadow_data, bool* has_header, struct bpf* bpf) {

  // If current values match, the shadow buffer is most up-to-date.
  if(current == shadow_tx_current) {
    return;
  }

  // We need to synchronize the ring buffer with the shadow ring
	// buffer. We need to watch out for a wrap in the ring.
  uint32_t n;
  if(current > shadow_tx_current) {
    // no wraparound
    n = current - shadow_tx_current;
  } else {
    // wraparound
    n = (DESCRING_ELEMENTS_N - shadow_tx_current) + current;
  }

  // Chunk the range in smaller ranges which we can formally verify.
  #define CHUNK_SIZE 64
  uint32_t chunks = n / CHUNK_SIZE;
  uint32_t cur_position = shadow_tx_current;

  // full chunks
  for(uint32_t i=0; i<chunks; i++) {
    #ifdef MODEL
    __CPROVER_assert(check_pos(cur_position), "tx_tos_iterator #1");
    __CPROVER_assert(__CPROVER_rw_ok(nw_ring), "tx_tos_iterator #2");
    __CPROVER_assert(__CPROVER_rw_ok(shadow_ring), "tx_tos_iterator #3");
    __CPROVER_assert(__CPROVER_rw_ok(shadow_data), "tx_tos_iterator #4");
    __CPROVER_assert(__CPROVER_rw_ok(has_header,
        DESCRING_ELEMENTS_N * sizeof(bool)), "tx_tos_iterator #5");
    __CPROVER_assert(__CPROVER_rw_ok(bpf), "tx_tos_iterator #6");

    // To model that we called tx_tos_iterator for a certain index, we set
    // the sync variable. It is defined in the harness.
    extern bool sync2[8];
    sync2[i] = true;
    #else
    tx_tos_iterator2(cur_position, CHUNK_SIZE, nw_ring, shadow_ring, shadow_data,
        has_header, bpf);
    #endif

    cur_position = (cur_position + CHUNK_SIZE) % DESCRING_ELEMENTS_N;
  }

  // remainder
  uint32_t remainder = n % CHUNK_SIZE;

  #ifdef MODEL
  __CPROVER_assert(check_pos(cur_position), "tx_tos_iterator #6");
  __CPROVER_assert(remainder < CHUNK_SIZE, "tx_tos_iterator #7");
  __CPROVER_assert(__CPROVER_rw_ok(nw_ring), "tx_tos_iterator #9");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_ring), "tx_tos_iterator #10");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_data), "tx_tos_iterator #11");
  __CPROVER_assert(__CPROVER_rw_ok(has_header,
      DESCRING_ELEMENTS_N * sizeof(bool)), "tx_tos_iterator #12");

  // To model that we called tx_tos_iterator for a certain index, we set
  // the sync variable. It is defined in the harness.
  if(remainder > 0) {
    extern bool sync2[8];
    sync2[chunks] = true;
  }

  #else
  tx_tos_iterator2(cur_position, remainder, nw_ring, shadow_ring, shadow_data,
    has_header, bpf);
  #endif
}


/*
* - does access global state before calling dependent functions.
* - state needs to be initialized. ATF guarantees that.
* - We verify that we only write legal values back to the state (queue, current)
*   so that there are no harmful side effects to the global "state" object.
* - does not exhibit indeterministic behavior
* - queue and current can have arbitrary values
* - bpf is required to be initialized. ATF guarantees that.
*/
void tx_tos(uint32_t queue, uint32_t current) {
  if(!check_tx_queue(queue)) {
    ERROR("Invalid TX queue: %d\n", queue);
    return;
  }

  if(!check_pos(current)) {
    ERROR("Invalid cur_position: %d\n", current);
    return;
  }

  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(state.nw_tx_descrings[queue]), "tx_tos #0");
  #else
  if(!is_nw_ram_region((uint64_t) state.nw_tx_descrings[queue], DESCRING_SIZE_BYTES)) {
    ERROR("NW ring not correct: Not a NW RAM region: %llx, %d\n",
      (uint64_t) state.nw_tx_descrings[queue], DESCRING_SIZE_BYTES);
    return;
  }
  #endif
  struct descring* nw_ring = state.nw_tx_descrings[queue];

  struct descring* shadow_ring = state.shadow_tx_descrings[queue];
  if(!shadow_ring) {
    ERROR("Shadow ring is not initialized\n");
    return;
  }

  uint32_t shadow_tx_current = state.shadow_tx_current[queue];
  if(!check_pos(shadow_tx_current)) {
    ERROR("Invalid shadow_tx_current position: %d\n", shadow_tx_current);
    return;
  }

  struct dataring* shadow_data = state.tx_datarings[queue];
  if(!shadow_data) {
    ERROR("Shadow data ring is not initialized\n");
    return;
  }

  bool* has_header = &state.has_header[queue][0];

  struct bpf* bpf = &state.bpf;

  #ifdef MODEL
  __CPROVER_assert(check_pos(current), "tx_tos #1");
  __CPROVER_assert(check_pos(shadow_tx_current), "tx_tos #2");
  __CPROVER_assert(__CPROVER_rw_ok(nw_ring), "tx_tos #3");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_ring), "tx_tos #4");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_data), "tx_tos #5");
  __CPROVER_assert(__CPROVER_rw_ok(has_header,
      DESCRING_ELEMENTS_N * sizeof(bool)), "tx_tos #6");
  __CPROVER_assert(__CPROVER_rw_ok(bpf), "tx_tos #7");
  #else
  tx_tos_iterator(current, shadow_tx_current, nw_ring, shadow_ring,
    shadow_data, has_header, bpf);
  #endif

  #ifdef MODEL
  __CPROVER_assert(check_pos(current), "tx_tos #8");
  #endif

  state.shadow_tx_current[queue] = current;
}

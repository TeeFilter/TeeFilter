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

#include "teefilter_tx_frs.h"
#include "teefilter_tx_common.h"
#include "descring.h"
#include "dataring.h"
#include "plat/memcpy.h"
#include "checks.h"
#include "state.h"

/* -----------------------------------------------------------------------------
* TX_FRS
* --------------------------------------------------------------------------- */

/*
* - is not based on any sort of global state
* - does not exhibit indeterministic behavior
* - dest is required to be valid. Needs to be checked by caller!
* - origin is required to be valid. Needs to be checked by caller!
*/
void tx_frs_bd_handler(struct bufdesc_ex* dest, struct bufdesc_ex* origin) {
  #ifdef MODEL
  uint8_t* data = dest->desc.cbd_bufaddr;
  #else
  uint32_t data = le32toh(dest->desc.cbd_bufaddr);
  #endif

  copy_desc(dest, origin, data);
}


/*
* We build chunks of 64 elements if there are many multiple frames for
* tranmission. We build two iterators. An upper layer that iterates over the
* chunks and a lower layer that iterates over the buffer descriptors.
* Then, we prove them individually. This way, we are able to verify them.
* Without that, we would end up in a state explosion.
* - is not based on any sort of global state (except the sync variable for the model)
* - does not exhibit indeterministic behavior
* - current is required to be valid. Needs to be checked by caller!
* - elements is required to be valid. Needs to be checked by caller!
* - nw_ring is required to be valid. Needs to be checked by caller!
* - shadow_ring is required to be valid. Needs to be checked by caller!
*/
void tx_frs_iterator2(uint32_t current, uint32_t elements,
    struct descring* nw_ring, struct descring* shadow_ring) {

  for(uint32_t i=0; i<elements; i++) {
    uint32_t index = (current + i) % DESCRING_ELEMENTS_N;
    // We know that index is valid, i.e., in [0, DESCRING_ELEMENTS_N-1] here

    struct bufdesc_ex* origin = &shadow_ring->elements[index];

  	// We want to return false if we want to abort the loop process.
  	// We do only want to copy buffer descriptors that are already transmitted.
  	// This also means what we can free the data for them as they are already
  	// transmitted. For the others, we still need the data and cannot comsume
  	// the data ring entry.
  	// TX_READY means ready to transmit = not yet transmitted
    #ifdef MODEL
    uint16_t status = origin->desc.cbd_sc;
    #else
    uint16_t status = le16toh(origin->desc.cbd_sc);
    #endif

    // We overapproximate the solution in our model. If we would allow shortcuts,
    // the number of potential paths through the function explosed. An
    // overapproximation does not harm the validity of the proof.
    #ifndef MODEL_SKIP_SHORTCUT
    if(status & BD_ENET_TX_READY) {
      break;
    }
    #endif

    struct bufdesc_ex* dest = &nw_ring->elements[index];

    #ifdef MODEL
    __CPROVER_assert(__CPROVER_rw_ok(dest), "tx_tos_iterator #1");
    __CPROVER_assert(__CPROVER_rw_ok(origin), "tx_tos_iterator #2");
    __CPROVER_assert(check_pos(index), "tx_tos_iterator #3");
    // To model that we called tx_tos_bd_handler for a certain index, we set
    // the sync variable. It is defined in the harness.
    extern bool sync[DESCRING_ELEMENTS_N];
    sync[index] = true;
    #else
    tx_frs_bd_handler(dest, origin);
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
* - pending_tx_position eeds to be valid! Caller needs to ensure that!
* - shadow_tx_current needs to be valid! Caller needs to ensure that!
* - nw_ring needs to be a valid pointer. Caller needs to ensure that!
* - shadow_ring needs to be a valid pointer. Caller needs to ensure that!
*/
void tx_frs_iterator(uint32_t pending_tx_position, uint32_t shadow_tx_current,
    struct descring* nw_ring, struct descring* shadow_ring) {

  // If current values match, the shadow buffer is most up-to-date.
  if(pending_tx_position == shadow_tx_current) {
    return;
  }

  // We need to synchronize the ring buffer with the shadow ring
	// buffer. We need to watch out for a wrap in the ring.
  uint32_t n;
  if(pending_tx_position < shadow_tx_current) {
    // no wraparound
    n = shadow_tx_current - pending_tx_position;
  } else {
    // wraparound
    n = (DESCRING_ELEMENTS_N - pending_tx_position) + shadow_tx_current;
  }

  // Chunk the range in smaller ranges which we can formally verify.
  #define CHUNK_SIZE 64
  uint32_t chunks = n / CHUNK_SIZE;
  uint32_t cur_position = pending_tx_position;

  // full chunks
  for(uint32_t i=0; i<chunks; i++) {
    #ifdef MODEL
    __CPROVER_assert(check_pos(cur_position), "tx_frs_iterator #1");
    __CPROVER_assert(__CPROVER_rw_ok(nw_ring), "tx_frs_iterator #2");
    __CPROVER_assert(__CPROVER_rw_ok(shadow_ring), "tx_frs_iterator #3");

    // To model that we called tx_tos_iterator for a certain index, we set
    // the sync variable. It is defined in the harness.
    extern bool sync2[8];
    sync2[i] = true;

    #else
    tx_frs_iterator2(cur_position, CHUNK_SIZE, nw_ring, shadow_ring);
    #endif

    cur_position = (cur_position + CHUNK_SIZE) % DESCRING_ELEMENTS_N;
  }

  // remainder
  uint32_t remainder = n % CHUNK_SIZE;
  #ifdef MODEL
  __CPROVER_assert(check_pos(cur_position), "tx_frs_iterator #6");
  __CPROVER_assert(remainder < CHUNK_SIZE, "tx_frs_iterator #7");
  __CPROVER_assert(__CPROVER_rw_ok(nw_ring), "tx_frs_iterator #9");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_ring), "tx_frs_iterator #10");

  // To model that we called tx_tos_iterator for a certain index, we set
  // the sync variable. It is defined in the harness.
  extern bool sync2[8];
  sync2[chunks] = true;

  #else
  tx_frs_iterator2(cur_position, remainder, nw_ring, shadow_ring);
  #endif
}


/*
* - does access global state before calling dependent functions.
* - state needs to be initialized. ATF guarantees that.
* - Variables in state are only read but never written in this function. Thus,
*   there are no side effects on the global "state" object.
* - does not exhibit indeterministic behavior
* - queue and pending_tx_position can have arbitrary values
* - bpf is required to be initialized. ATF guarantees that.
*/
void tx_frs(uint32_t queue, uint32_t pending_tx_position) {
  if(!check_tx_queue(queue)) {
    ERROR("Invalid TX queue: %d\n", queue);
    return;
  }

  if(!check_pos(pending_tx_position)) {
    ERROR("Invalid pending_tx_position: %d\n", pending_tx_position);
    return;
  }

  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(state.nw_tx_descrings[queue]), "tx_frs #0");
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

  #ifdef MODEL
  __CPROVER_assert(check_pos(pending_tx_position), "tx_frs #1");
  __CPROVER_assert(check_pos(shadow_tx_current), "tx_frs #2");
  __CPROVER_assert(__CPROVER_rw_ok(nw_ring), "tx_frs #3");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_ring), "tx_frs #4");
  #else
  tx_frs_iterator(pending_tx_position, shadow_tx_current, nw_ring,
      shadow_ring);
  #endif
}

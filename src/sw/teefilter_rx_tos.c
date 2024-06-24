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
#include <endian.h>

#include "teefilter_rx_tos.h"
#include "teefilter_rx_common.h"
#include "descring.h"
#include "dataring.h"
#include "plat/memcpy.h"
#include "checks.h"
#include "state.h"

/* -----------------------------------------------------------------------------
* RX_TOS
* --------------------------------------------------------------------------- */

/*
* - is not based on any sort of global state
* - does not exhibit indeterministic behavior
* - dest is required to be valid. Needs to be checked by caller!
* - origin is required to be valid. Needs to be checked by caller!
* - index is required to be valid. Needs to be checked by caller!
* - element is required to be valid. Needs to be checked by caller!
*/
void rx_tos_bd_handler(struct bufdesc_ex* dest, struct bufdesc_ex* origin,
    uint32_t index, struct element* element) {

  #ifdef MODEL
	uint16_t status = origin->desc.cbd_sc;
  #else
	uint16_t status = le16toh(origin->desc.cbd_sc);
  #endif

  // We have received new data. The NW resets the buffer descriptor.
  // We copy over the status and set the data pointer to the corresponding
  // buffer descriptor in the shadow ring.
  #ifdef MODEL
  uint8_t* newData = (uint8_t*) element;
  #else
  // We do not model real addresses. On real hardware, the NIC can only
  // access 32-bit memory via DMA. If the address is not valid,
  // it is okay that the buffer descriptor is NOT synchronized and the
  // function just returns. This might lead to inavailability of the network,
  // however, we never guarantee inavailability. We guatantee that IF the NW
  //  network stack acts in accordance, network functionality is possible
  // and filtering is conducted.
  if(((uint64_t) element) > 0xFFFFFFFF) {
    ERROR("Address too large\n");
    return;
  }
  uint32_t newData = (uint32_t) ((uint64_t) element);
  #endif

  // Verify that BD wraps are correctly handled
  if(index == DESCRING_ELEMENTS_N - 1 && (status & BD_SC_WRAP) == 0x0) {
    ERROR("rx_handle_tos: Last descriptor does not WRAP\n");
    origin->desc.cbd_sc = status | BD_SC_WRAP;
  }

  copy_desc(dest, origin, newData);
}


/*
* - is not based on any sort of global state (except the sync variable for the model)
* - does not exhibit indeterministic behavior
* - current is required to be valid. Needs to be checked by caller!
* - received is required to be valid. Needs to be checked by caller!
* - nw_ring is required to be valid. Needs to be checked by caller!
* - shadow_ring is required to be valid. Needs to be checked by caller!
* - shadow_data is required to be valid. Needs to be checked by caller!
*/
void rx_tos_iterator(uint32_t current, uint32_t received, struct descring* nw_ring,
    struct descring* shadow_ring, struct dataring* shadow_data) {

  for(uint32_t i=0; i<received; i++) {
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
    __CPROVER_assert(__CPROVER_rw_ok(dest), "rx_tos_iterator #1");
    __CPROVER_assert(__CPROVER_rw_ok(origin), "rx_tos_iterator #2");
    __CPROVER_assert(check_pos(index), "rx_tos_iterator #3");
    __CPROVER_assert(__CPROVER_rw_ok(element), "rx_tos_iterator #4");
    // To model that we called rx_tos_bd_handler for a certain index, we set
    // the sync variable. It is defined in the harness.
    extern bool sync[DESCRING_ELEMENTS_N];
    sync[index] = true;
    #else
    rx_tos_bd_handler(dest, origin, index, element);
    #endif
  }
}


/*
* - does access global state before calling dependent functions.
* - state needs to be initialized. ATF guarantees that.
* - Variables in state are only read but never written in this function. Thus,
*   there are no side effects on the global "state" object.
* - does not exhibit indeterministic behavior
* - queue, current, and received can have arbitrary values
* - bpf is required to be initialized. ATF guarantees that.
*/
void rx_tos(uint32_t queue, uint32_t current, uint32_t received) {
  if(!check_rx_queue(queue)) {
    ERROR("Invalid RX queue: %d\n", queue);
    return;
  }

  if(!check_pos(current)) {
    ERROR("Invalid current: %d\n", current);
    return;
  }

  if(!check_budget(received)) {
    ERROR("Invalid value for received: %d\n", received);
    return;
  }

  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok(state.nw_rx_descrings[queue]), "rx_tos #0");
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

  #ifdef MODEL
  __CPROVER_assert(check_pos(current), "rx_tos #1");
  __CPROVER_assert(check_budget(received), "rx_tos #2");
  __CPROVER_assert(__CPROVER_rw_ok(nw_ring), "rx_tos #3");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_ring), "rx_tos #4");
  __CPROVER_assert(__CPROVER_rw_ok(shadow_data), "rx_tos #5");
  #else
  rx_tos_iterator(current, received, nw_ring, shadow_ring, shadow_data);
  #endif
}

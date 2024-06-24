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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "teefilter_rx_frs.h"
#include "teefilter_common.h"
#include "teefilter_init.h"
#include "teefilter_rx_common.h"
#include "certrbpf.h"
#include "state.h"
#include "checks.h"
#include "dataring.h"


void harness_rx_frs_frame_handler_negative() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  certrbpf_init(&state.bpf); // guaranteed by ATF on real hardware

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  #define NW_BUFFER_SIZE 2048 // larger than the actual size
  uint8_t* dstData = malloc(NW_BUFFER_SIZE);
  __CPROVER_assume(dstData != NULL);


  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  uint32_t originSize;
  uint8_t* originData = malloc(originSize);
  __CPROVER_assume(originData != NULL);

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  rx_frs_frame_handler(dstData, originData, originSize, &state.bpf);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  // We assume a NEGATIVE verdict of the filter
  for(uint32_t i=0; i<FEC_MAX_FRAME_LEN; i++) {
    __CPROVER_assert(dstData[i] == 0x0, "harness_rx_handle_data_negative #1");
  }

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/

  free(dstData);
  free(originData);
}


void harness_rx_frs_frame_handler_positive() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  certrbpf_init(&state.bpf); // guaranteed by ATF on real hardware

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  uint32_t originSize;

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assume(check_rx_packet_size(originSize));
  uint8_t* originData = malloc(originSize);
  __CPROVER_assume(originData != NULL);

  #define NW_BUFFER_SIZE 2048 // larger than the actual size
  uint8_t* dstData = malloc(NW_BUFFER_SIZE);
  __CPROVER_assume(dstData != NULL);

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  rx_frs_frame_handler(dstData, originData, originSize, &state.bpf);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  // We additionally assume a POSITIVE verdict of the filter via the precompiler
  // flag MODEL_ASSUME_POSITIVE_VERDICT in the Makefile.
  __CPROVER_assert(memcmp(dstData, originData, originSize) == 0,
    "harness_rx_frs_frame_handler_positive #1");

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/

  free(dstData);
  free(originData);
}


void harness_rx_frs_bd_handler_negative() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  struct bufdesc_ex origin;
  struct bufdesc_ex dest;
  struct element element;
  uint32_t index;

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assume(check_pos(index));

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  rx_frs_bd_handler(&dest, &origin, index, &element, &state.bpf);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  /* No postconditions! If the data in the passed structs is not valid,
  * it is okay that the buffer descriptor is NOT synchronized but the
  * function just returns. This might lead to inavailability of the network,
  * however, we never guarantee inavailability. We guatantee that IF the NW
  * network stack acts in accordance, network functionality is possible
  * and filtering is conducted.
  */

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


void harness_rx_frs_bd_handler_positive() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  struct bufdesc_ex origin;
  struct bufdesc_ex dest;
  struct element element;
  uint32_t index;

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  origin.desc.cbd_bufaddr = (uint8_t*) &element;
  __CPROVER_assume(check_rx_packet_size(origin.desc.cbd_datlen));

  __CPROVER_assume(check_pos(index));

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  rx_frs_bd_handler(&dest, &origin, index, &element, &state.bpf);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assert(dest.desc.cbd_datlen == origin.desc.cbd_datlen, "harness_rx_frs_bd_handler #1");
  __CPROVER_assert(dest.desc.cbd_sc == origin.desc.cbd_sc, "harness_rx_frs_bd_handler #2");

  __CPROVER_assert(dest.cbd_esc == origin.cbd_esc, "harness_rx_frs_bd_handler #3");
  __CPROVER_assert(dest.cbd_prot == origin.cbd_prot, "harness_rx_frs_bd_handler #4");
  __CPROVER_assert(dest.cbd_bdu == origin.cbd_bdu, "harness_rx_frs_bd_handler #5");
  __CPROVER_assert(dest.ts == origin.ts, "harness_rx_frs_bd_handler #6");

  __CPROVER_assert(dest.res0[0] == origin.res0[0], "harness_rx_frs_bd_handler #7");
  __CPROVER_assert(dest.res0[1] == origin.res0[1], "harness_rx_frs_bd_handler #8");
  __CPROVER_assert(dest.res0[2] == origin.res0[2], "harness_rx_frs_bd_handler #9");
  __CPROVER_assert(dest.res0[3] == origin.res0[3], "harness_rx_frs_bd_handler #10");

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


bool sync[DESCRING_ELEMENTS_N];

void harness_rx_frs_iterator() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  uint32_t current;
  uint32_t budget;

  struct descring nw_ring;
  struct descring shadow_ring;
  struct dataring shadow_data;

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assume(check_pos(current));
  __CPROVER_assume(check_budget(budget));

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  rx_frs_iterator(current, budget, &nw_ring, &shadow_ring, &shadow_data,
      &state.bpf);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  for(uint32_t i=0; i<budget; i++) {
    uint32_t index = (current + i) % DESCRING_ELEMENTS_N;
    __CPROVER_assert(sync[index], "harness_rx_frs_iterator #1");
  }

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


void harness_rx_frs() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  uint32_t queue;
  uint32_t current;
  uint32_t budget;

  // TeeFilter initialization guaranteed by ATF.

  teefilter_init();

  struct descring shadow_rx_descrings[3];
  state.shadow_rx_descrings[0] = &shadow_rx_descrings[0];
  state.shadow_rx_descrings[1] = &shadow_rx_descrings[1];
  state.shadow_rx_descrings[2] = &shadow_rx_descrings[2];

  struct descring nw_rx_descrings[3];
  state.nw_rx_descrings[0] = &nw_rx_descrings[0];
  state.nw_rx_descrings[1] = &nw_rx_descrings[1];
  state.nw_rx_descrings[2] = &nw_rx_descrings[2];

  struct dataring shadow_data[3];
  state.rx_datarings[0] = &shadow_data[0];
  state.rx_datarings[1] = &shadow_data[1];
  state.rx_datarings[2] = &shadow_data[2];

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  rx_frs(queue, current, budget);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}

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

#include "teefilter_rx_tos.h"
#include "teefilter_common.h"
#include "teefilter_rx_common.h"
#include "state.h"
#include "checks.h"


void harness_tx_frs_bd_handler() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  struct bufdesc_ex dest;
  struct bufdesc_ex origin;

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  tx_frs_bd_handler(&dest, &origin);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assert(dest.desc.cbd_datlen == origin.desc.cbd_datlen, "harness_tx_tos_bd_handler_positive #1");
  __CPROVER_assert(dest.desc.cbd_sc == origin.desc.cbd_sc, "harness_tx_tos_bd_handler_positive #2");

  __CPROVER_assert(dest.cbd_esc == origin.cbd_esc, "harness_tx_tos_bd_handler_positive #3");
  __CPROVER_assert(dest.cbd_prot == origin.cbd_prot, "harness_tx_tos_bd_handler_positive #4");
  __CPROVER_assert(dest.cbd_bdu == origin.cbd_bdu, "harness_tx_tos_bd_handler_positive #5");
  __CPROVER_assert(dest.ts == origin.ts, "harness_tx_tos_bd_handler_positive #6");

  __CPROVER_assert(dest.res0[0] == origin.res0[0], "harness_tx_tos_bd_handler_positive #7");
  __CPROVER_assert(dest.res0[1] == origin.res0[1], "harness_tx_tos_bd_handler_positive #8");
  __CPROVER_assert(dest.res0[2] == origin.res0[2], "harness_tx_tos_bd_handler_positive #9");
  __CPROVER_assert(dest.res0[3] == origin.res0[3], "harness_tx_tos_bd_handler_positive #10");

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


bool sync[DESCRING_ELEMENTS_N];

void harness_tx_frs_iterator2() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  uint32_t current;
  uint32_t elements;

  struct descring nw_ring;
  struct descring shadow_ring;

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assume(check_pos(current));

  // We build chunks of 64 elements if there are many multiple frames for
  // tranmission. We build two iterators. An upper layer that iterates over the
  // chunks and a lower layer that iterates over the buffer descriptors.
  // Then, we prove them individually. This way, we are able to verify them.
  // Without that, we would end up in a state explosion.
  __CPROVER_assume(elements <= 64);

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  tx_frs_iterator2(current, elements, &nw_ring, &shadow_ring);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  for(uint32_t i=0; i<elements; i++) {
    uint32_t index = (current + i) % DESCRING_ELEMENTS_N;
    __CPROVER_assert(sync[index], "harness_tx_frs_iterator2 #1");
  }

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


bool sync2[8];

void harness_tx_frs_iterator() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  uint32_t pending_tx_position;
  uint32_t shadow_tx_current;

  struct descring nw_ring;
  struct descring shadow_ring;

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assume(check_pos(pending_tx_position));
  __CPROVER_assume(check_pos(shadow_tx_current));

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  tx_frs_iterator(pending_tx_position, shadow_tx_current, &nw_ring, &shadow_ring);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  uint32_t n;
  if(pending_tx_position <= shadow_tx_current) {
    // no wraparound
    n = shadow_tx_current - pending_tx_position;
  } else {
    // wraparound
    n = (DESCRING_ELEMENTS_N - pending_tx_position) + shadow_tx_current;
  }

  uint32_t chunks = n / 64;
  for(uint32_t i=0; i<chunks; i++) {
    __CPROVER_assert(sync2[i], "harness_tx_frs_iterator #1");
  }

  uint32_t remainder = n % 64;
  if(remainder > 0) {
    __CPROVER_assert(sync2[chunks], "harness_tx_frs_iterator #2");
  }

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


void harness_tx_frs() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  uint32_t queue;
  uint32_t pending_tx_position;

  // TeeFilter initialization guaranteed by ATF.

  teefilter_init();

  struct descring shadow_tx_descrings[3];
  state.shadow_tx_descrings[0] = &shadow_tx_descrings[0];
  state.shadow_tx_descrings[1] = &shadow_tx_descrings[1];
  state.shadow_tx_descrings[2] = &shadow_tx_descrings[2];

  struct descring nw_tx_descrings[3];
  state.nw_tx_descrings[0] = &nw_tx_descrings[0];
  state.nw_tx_descrings[1] = &nw_tx_descrings[1];
  state.nw_tx_descrings[2] = &nw_tx_descrings[2];

  struct dataring shadow_data[3];
  state.tx_datarings[0] = &shadow_data[0];
  state.tx_datarings[1] = &shadow_data[1];
  state.tx_datarings[2] = &shadow_data[2];

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  tx_frs(queue, pending_tx_position);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}

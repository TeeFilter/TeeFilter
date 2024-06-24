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

#include "teefilter_init.h"
#include "state.h"
#include "checks.h"

void harness_teefilter_init() {
  /* -------------------------------------------------------------------------*/
  // Initialize TeeFilter
  /* -------------------------------------------------------------------------*/

  teefilter_init();

  /* -------------------------------------------------------------------------*/
  // Verify invariants after initialization of TeeFilter
  /* -------------------------------------------------------------------------*/

	for(uint32_t i=0; i<NUMBER_TX_QUEUES; i++) {
    __CPROVER_assert(state.shadow_tx_current[i] == 0, "harness_teefilter_init #1");
  }

	for(uint32_t i=0; i<NUMBER_TX_QUEUES; i++) {
    for(uint32_t j=0; j<DATARING_ELEMENTS_N; j++) {
      __CPROVER_assert(state.has_header[i][j] == true, "harness_teefilter_init #2");
    }
	}

	for(uint32_t i=0; i<NUMBER_TX_QUEUES; i++) {
    __CPROVER_assert(state.nw_tx_descrings[i] == NULL, "harness_teefilter_init #4");
	}

	for(uint32_t i=0; i<NUMBER_RX_QUEUES; i++) {
    __CPROVER_assert(state.nw_rx_descrings[i] == NULL, "harness_teefilter_init #3");
	}

  __CPROVER_assert(state.shadow_rx_descrings[0] == (struct descring*) ((uint64_t)  SHADOW_DESCRINGS_BASE + RECEIVE_0_OFFSET), "harness_teefilter_init #4");

  __CPROVER_assert(state.shadow_rx_descrings[1] == (struct descring*) ((uint64_t)  SHADOW_DESCRINGS_BASE + RECEIVE_1_OFFSET), "harness_teefilter_init #5");

  __CPROVER_assert(state.shadow_rx_descrings[2] == (struct descring*) ((uint64_t)  SHADOW_DESCRINGS_BASE + RECEIVE_2_OFFSET), "harness_teefilter_init #6");

  __CPROVER_assert(state.shadow_tx_descrings[0] == (struct descring*) ((uint64_t)  SHADOW_DESCRINGS_BASE + TRANSMIT_0_OFFSET), "harness_teefilter_init #7");

  __CPROVER_assert(state.shadow_tx_descrings[1] == (struct descring*) ((uint64_t)  SHADOW_DESCRINGS_BASE + TRANSMIT_1_OFFSET), "harness_teefilter_init #8");

  __CPROVER_assert(state.shadow_tx_descrings[2] == (struct descring*) ((uint64_t)  SHADOW_DESCRINGS_BASE + TRANSMIT_2_OFFSET), "harness_teefilter_init #9");

  __CPROVER_assert(state.rx_datarings[0] == (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_RECEIVE_0_OFFSET), "harness_teefilter_init #10");

  __CPROVER_assert(state.rx_datarings[1] == (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_RECEIVE_1_OFFSET), "harness_teefilter_init #11");

  __CPROVER_assert(state.rx_datarings[2] == (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_RECEIVE_2_OFFSET), "harness_teefilter_init #12");

  __CPROVER_assert(state.tx_datarings[0] == (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_TRANSMIT_0_OFFSET), "harness_teefilter_init #13");

  __CPROVER_assert(state.tx_datarings[1] == (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_TRANSMIT_1_OFFSET), "harness_teefilter_init #14");

  __CPROVER_assert(state.tx_datarings[2] == (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_TRANSMIT_2_OFFSET), "harness_teefilter_init #15");
}

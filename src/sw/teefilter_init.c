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

#include "teefilter_init.h"

#include "state.h"
#include "descring.h"
#include "dataring.h"
#include "certrbpf.h"

/* -----------------------------------------------------------------------------
* Public Interface
* --------------------------------------------------------------------------- */

bool teefilter_init() {

  // shadow_tx_current
	for(uint32_t i=0; i<NUMBER_TX_QUEUES; i++) {
		state.shadow_tx_current[i] = 0x0;
	}

  // has_header
	for(uint32_t i=0; i<NUMBER_TX_QUEUES; i++) {
    for(uint32_t j=0; j<DATARING_ELEMENTS_N; j++) {
		    state.has_header[i][j] = true;
    }
	}

  /* Initialize the state of the framework */
  // nw_tx_descrings
	for(uint32_t i=0; i<NUMBER_RX_QUEUES; i++) {
		state.nw_rx_descrings[i] = NULL;
	}

  // nw_rx_descrings
	for(uint32_t i=0; i<NUMBER_TX_QUEUES; i++) {
		state.nw_tx_descrings[i] = NULL;
	}

	// Initialize descrings so that they point to the reserved memory
  // shadow_rx_descrings
	state.shadow_rx_descrings[0] = (struct descring*) ((uint64_t) SHADOW_DESCRINGS_BASE + RECEIVE_0_OFFSET);
	state.shadow_rx_descrings[1] = (struct descring*) ((uint64_t) SHADOW_DESCRINGS_BASE + RECEIVE_1_OFFSET);
	state.shadow_rx_descrings[2] = (struct descring*) ((uint64_t) SHADOW_DESCRINGS_BASE + RECEIVE_2_OFFSET);
  // shadow_tx_descrings
	state.shadow_tx_descrings[0] = (struct descring*) ((uint64_t) SHADOW_DESCRINGS_BASE + TRANSMIT_0_OFFSET);
	state.shadow_tx_descrings[1] = (struct descring*) ((uint64_t) SHADOW_DESCRINGS_BASE + TRANSMIT_1_OFFSET);
	state.shadow_tx_descrings[2] = (struct descring*) ((uint64_t) SHADOW_DESCRINGS_BASE + TRANSMIT_2_OFFSET);

	// Initialize the datarings so they point to the reserved memory
  // rx_datarings
	state.rx_datarings[0] = (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_RECEIVE_0_OFFSET);
	state.rx_datarings[1] = (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_RECEIVE_1_OFFSET);
	state.rx_datarings[2] = (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_RECEIVE_2_OFFSET);
  // tx_datarings
	state.tx_datarings[0] = (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_TRANSMIT_0_OFFSET);
	state.tx_datarings[1] = (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_TRANSMIT_1_OFFSET);
	state.tx_datarings[2] = (struct dataring*) ((uint64_t) DATARING_BASE + DATARING_TRANSMIT_2_OFFSET);

  return true;
}

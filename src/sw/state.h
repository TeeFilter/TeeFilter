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

#ifndef STATE_H
#define STATE_H

#include <stdint.h>

#include "descring.h"
#include "dataring.h"
#include "teefilter_common.h"

#include "certrbpf_interpreter.h"
#include "certrbpf_verifier.h"

/* -----------------------------------------------------------------------------
* Definition of the current state of the framework
* --------------------------------------------------------------------------- */

#define BPF_STACK_SIZE 512
#define BPF_DYNAMIC_RULE_SIZE 1024

/* State abstraction for the eBPF interpreter */
struct bpf {
  // Did we verify (initialize) the current execution state
  bool initialized;

  // Current execution state
  struct bpf_state bpf_state;
  struct memory_region regions[2];
  uint8_t stack[BPF_STACK_SIZE];

  // Dynamic rule buffer and its state
  uint8_t dynamic_rule[BPF_DYNAMIC_RULE_SIZE];
  uint32_t dynamic_rule_length;
  bool dynamic_rule_enabled;
};

/*
* We wrap the state of the framework in a custom struct and provide a getter
* since this makes it easier to formally verify the framework for memory safety.
* This is because the getter can be easily called from within the harness.
*/
struct state {

  /*
  * Stores the physical NW addresses of the NW TX and RX queues. This is the
  * value the NIC driver tries to write to the NIC configuration registers. If
  * the NW driver later on reads from the register, it should retrieve the value
  * it expects and not the SW address to the shadow ring buffer. Moreover, the
  * SW uses these addresses as base to read data from the NW and write data to
  * the NW.
  */
  struct descring* nw_tx_descrings[NUMBER_TX_QUEUES];
  struct descring* nw_rx_descrings[NUMBER_RX_QUEUES];

  /*
  * Stores the physical SW addresses of the SW TX and RX queues. This the value
  * that is actually written to the NIC configuration registers. The SW uses
  * these registers as base for any communication with the NIC via buffer
  * descriptors. These registers are only accessed by the NIC and by the SW.
  */
  struct descring* shadow_tx_descrings[NUMBER_TX_QUEUES];
  struct descring* shadow_rx_descrings[NUMBER_RX_QUEUES];

  /*
  * Stores pointers to the data rings that hold the actual Ethernet frames
  * so that we can prevent TOCTOU race conditions.
  */
  struct dataring* tx_datarings[NUMBER_TX_QUEUES];
  struct dataring* rx_datarings[NUMBER_RX_QUEUES];

  /*
  * cur in the NW points to the first free element in the ring buffer.
  * tx_pending in the NW points to the first element that is not yet acknowledged by
  * the NIC. We found out that we do NOT need a shadow version of tx_pending,
  * since we are not interested in the package status in the SW. We only need
  * a shadow version of cur so that we now which packages to copy TO the shadow
  * buffer. The NW can then tell us its pending_tx and we copy BACK the interval
  * from [pending_tx, shadow_cur).
  * In the case of `tos`, we handle the data in the interval [shadow_cur, cur).
  * Initially, shadow_tx_current points to the base of the ring. This indicates
  * that no data is available. Thus, we initialize the ring accordingly.
  * We store the value as index in the ring buffer.
  */
  uint32_t shadow_tx_current[NUMBER_TX_QUEUES];

  /*
  * We store the information whether the next element in the ring buffer has
  * a header. This is dependent on the previous element and whether the
  * BD_ENET_TX_LAST flag has been set. We need to check and copy all elements
  * that contain a header but may refrain from copying payload only data packets.
  * We do NOT need it for the RX queues, since every received packet needs to
  * have a header.
  */
  bool has_header[NUMBER_TX_QUEUES][DATARING_ELEMENTS_N];

  /*
  * The nonce for updating the TeeFilter filtering rules.
  */
  uint64_t nonce;

  /*
  * The state of the eBPF interpreter.
  */
  struct bpf bpf;
};


/* -----------------------------------------------------------------------------
* Global State
* --------------------------------------------------------------------------- */

extern struct state state;

#endif

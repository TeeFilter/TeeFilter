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

#include "checks.h"

#include "teefilter_common.h"
#include "teefilter_rx_common.h"
#include "descring.h"
#include "dataring.h"

/* -----------------------------------------------------------------------------
* is_in_nic_mmio_space
* --------------------------------------------------------------------------- */

/*
* - is not based on any sort of global state
* - does not exhibit indeterministic behavior
* - no prior restrictions on address
*/
bool is_word_in_nic_mmio_space(uint64_t address) {
  if(address % 0x4 != 0) {
    return false;
  }

  uint64_t x1 = address;
  if (address > UINT64_MAX - 4) {
    // address way too big to be realistic
    return false;
  }
  uint64_t x2 = address + 4 -1; // ranges are inclusive

  // First check if we are a valid address to RAM
  uint64_t y1 = IMX_NIC_BASE;
  uint64_t y2 = IMX_NIC_BASE + (uint64_t) IMX_NIC_SIZE-1; // ranges are inclusive
  bool nic = x1 <= y2 && y1 <= x2;
  return nic;
}


/* -----------------------------------------------------------------------------
* is_nw_ram_region
* --------------------------------------------------------------------------- */

/*
* - is not based on any sort of global state
* - does not exhibit indeterministic behavior
* - no prior restrictions on address and size
*/
bool is_nw_ram_region(uint64_t address, uint32_t size) {
  uint64_t x1 = address;
  if (address > UINT64_MAX - size) {
    // RAM address or size way too big to be realistic
    return false;
  }
  uint64_t x2 = address + size;

  // First check if we are a valid address to RAM
  uint64_t y1 = IMX_DRAM_BASE;
  uint64_t y2 = IMX_DRAM_BASE + (uint64_t) IMX_DRAM_SIZE;
  bool ram = x1 <= y2 && y1 <= x2;
  if(!ram) {
    return false;
  }

  // Then check whether we point to SW memory
  uint64_t z1 = PROT_SECURE_MEM_AREA_START;
  uint64_t z2 = PROT_SECURE_MEM_AREA_STOP-1; // ranges are inclusive
  bool sw = x1 <= z2 && z1 <= x2;
  return !sw;
}

/* -----------------------------------------------------------------------------
* other checks
* --------------------------------------------------------------------------- */

bool check_tx_queue(uint32_t queue) {
  return queue < NUMBER_TX_QUEUES;
}

bool check_rx_queue(uint32_t queue) {
  return queue < NUMBER_RX_QUEUES;
}

bool check_pos(uint32_t pos) {
  return pos < DESCRING_ELEMENTS_N;
}

bool check_budget(uint32_t budget) {
  return budget <= NAPI_POLL_WEIGHT;
}

bool check_rx_packet_size(uint64_t size) {
  return size <= FEC_MAX_FRAME_LEN;
}

bool check_tx_packet_size(uint64_t size) {
  return size <= DATARING_ELEMENT_SIZE_BYTES;
}

bool check_direction(uint32_t direction) {
  return direction <= 1;
}

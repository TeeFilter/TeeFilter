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

#ifndef CHECKS_H
#define CHECK_H

#include <stdint.h>
#include <stdbool.h>

/* -----------------------------------------------------------------------------
* Secure RAM region that need to be protected from illegal acceses from the
* normal world. The actual protection is done by the TZC380. Here, however, we
* need to know these values to verify the addresses that we are passed from the
* normal world.
* --------------------------------------------------------------------------- */

#define PROT_SECURE_MEM_AREA_START 0xA0000000
#define PROT_SECURE_MEM_AREA_STOP 0xA0C00000

#define NAPI_POLL_WEIGHT 64

/* -----------------------------------------------------------------------------
* Public Interface
* --------------------------------------------------------------------------- */

bool is_word_in_nic_mmio_space(uint64_t address);

bool is_nw_ram_region(uint64_t address, uint32_t size);

bool check_tx_queue(uint32_t queue);
bool check_rx_queue(uint32_t queue);

bool check_pos(uint32_t pos);
bool check_budget(uint32_t budget);

bool check_rx_packet_size(uint64_t size);
bool check_tx_packet_size(uint64_t size);
bool check_direction(uint32_t direction);


#endif

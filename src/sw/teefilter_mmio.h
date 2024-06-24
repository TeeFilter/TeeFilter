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

#ifndef TEEFILTER_MMIO_H
#define TEEFILTER_MMIO_H

#include <stdint.h>

/* -----------------------------------------------------------------------------
* NIC MMIO register offsets for the addresses to the descriptor rings
* These have been extracted from the manual.
* --------------------------------------------------------------------------- */

#define ENET_ECR UL(0x24)
#define ENET_RCR UL(0x84)
#define ENET_TCR UL(0xC4)
#define ENET_PALR UL(0xE4)
#define ENET_PAUR UL(0xE8)
#define ENET_RDSR1	UL(0x160) /* Receive descriptor ring 1 */
#define ENET_TDSR1	UL(0x164) /* Transmit descriptor ring 1 */
#define ENET_MRBR1	UL(0x168) /* Maximum receive buff ring 1 size */
#define ENET_RDSR2	UL(0x16c) /* Receive descriptor ring 2 */
#define ENET_TDSR2	UL(0x170) /* Transmit descriptor ring 2 */
#define ENET_MRBR2	UL(0x174) /* Maximum receive buff ring 2 size */
#define ENET_RDSR0	UL(0x180) /* Receive descriptor ring 0 */
#define ENET_TDSR0	UL(0x184) /* Transmit descriptor ring 0 */
#define ENET_MRBR0	UL(0x188) /* Maximum receive buff ring 0 size */
#define ENET_FTRL UL(0x1B0)
#define ENET_TACC UL(0x1C0)
#define ENET_RACC UL(0x1C4)
#define ENET_QOS UL(0x1F0)

/* -----------------------------------------------------------------------------
* Public Interface.
* --------------------------------------------------------------------------- */

void teefilter_write32(uint32_t val, uint64_t address);

uint32_t teefilter_read32(uint64_t address);

#endif

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

#ifndef TEEFILTER_COMMON_H
#define TEEFILTER_COMMON_H

#include "descring.h"

/* -----------------------------------------------------------------------------
* Number of transmit and receive queues
* --------------------------------------------------------------------------- */

#define NUMBER_RX_QUEUES 3
#define NUMBER_TX_QUEUES 3

/* -----------------------------------------------------------------------------
* Flags for the buffer descriptor attribute field
* --------------------------------------------------------------------------- */

#define BD_SC_WRAP				((uint16_t)0x2000)	/* Last buffer descriptor */
#define BD_ENET_TX_READY	((uint16_t)0x8000) /* Ready to transmit */
#define BD_ENET_TX_LAST		((uint16_t)0x0800) /* Last BD in frame */
#define BD_ENET_RX_EMPTY	((uint16_t)0x8000) /* RX entry empty */
#define BD_ENET_RX_INT		((uint32_t)0x00800000) /* EXTENDED BD: IRQ when RX */

/* -----------------------------------------------------------------------------
* Memory Barriers
* --------------------------------------------------------------------------- */

// Those were ported from Linux in order to ensure the same behavior as in the
// original driver.

#define linux_dsb(opt)	asm volatile("dsb " #opt : : : "memory")
#define linux_dmb(opt)	asm volatile("dmb " #opt : : : "memory")
#define linux_wmb()		linux_dsb(st)
#define linux_dma_wmb()	linux_dmb(oshst)

/* -----------------------------------------------------------------------------
* Filter Direction
* --------------------------------------------------------------------------- */

#define DIRECTION_INBOUND 0x0
#define DIRECTION_OUTBOUND 0x1

/* -----------------------------------------------------------------------------
* Destroy Function
* --------------------------------------------------------------------------- */

void destroy(uint8_t* buffer, uint32_t size);

#ifdef MODEL
void copy_desc(struct bufdesc_ex* dest, struct bufdesc_ex* src,
    uint8_t* new_data_addr);
#else
void copy_desc(struct bufdesc_ex* dest, struct bufdesc_ex* src,
    uint32_t new_data_addr);
#endif

#endif

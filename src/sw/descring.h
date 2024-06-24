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

#ifndef DESCRING_H
#define DESCRING_H

#include <assert.h>
#include <stdint.h>
#include <common/debug.h>

/* -----------------------------------------------------------------------------
* Information about the descriptor rings and their elements.
* These have been extracted from the NIC driver.
* 0x4000 Bytes = 4 Pages a 4096B per ring
* --------------------------------------------------------------------------- */

#define DESCRING_SIZE_BYTES 0x4000
#define DESCRING_ELEMENT_SIZE_BYTES 32
#define DESCRING_ELEMENTS_N 512

/* -----------------------------------------------------------------------------
* Information about the shadow descriptor rings and their elements.
* These have been extracted from the NIC driver.
*
* We manually partition the shadow buffer as follows, mimicking the layout
* of the original ring buffers:
* 0xA0200000 - 0xA0204000: Receive descriptor ring 0
* 0xA0204000 - 0xA0208000: Receive descriptor ring 1
* 0xA0208000 - 0xA020c000: Receive descriptor ring 2
* 0xA020c000 - 0xA0210000: Transmit descriptor ring 0
* 0xA0210000 - 0xA0214000: Transmit descriptor ring 1
* 0xA0214000 - 0xA0218000: Transmit descriptor ring 2
*
* 0x4000 Bytes = 4 Pages a 4096B per ring
* --------------------------------------------------------------------------- */

#define SHADOW_DESCRINGS_BASE 0xA0200000
// #define SHADOW_DESCRINGS_SIZE_BYTES 0x200000

#define RECEIVE_0_OFFSET 0 * DESCRING_SIZE_BYTES
#define RECEIVE_1_OFFSET 1 * DESCRING_SIZE_BYTES
#define RECEIVE_2_OFFSET 2 * DESCRING_SIZE_BYTES

#define TRANSMIT_0_OFFSET 3 * DESCRING_SIZE_BYTES
#define TRANSMIT_1_OFFSET 4 * DESCRING_SIZE_BYTES
#define TRANSMIT_2_OFFSET 5 * DESCRING_SIZE_BYTES

/* -----------------------------------------------------------------------------
* Buffer Descriptor Definition.
* --------------------------------------------------------------------------- */

// The NIC uses little-endian internally, the CPU is big-endian convert with:
// le16toh, ..., htole16, ...
// https://github.com/ARM-software/arm-trusted-firmware/blob/master/include/lib/libc/endian.h
#define __fec32 uint32_t
#define __fec16 uint16_t

/*
* Simple buffer descriptor format, for more information see the Nitrogen8M
* user manual.
*/
struct bufdesc {
	__fec16 cbd_datlen;	/* Data length */
	__fec16 cbd_sc;		/* Control and status info */
	#ifdef MODEL
	uint8_t* cbd_bufaddr; /* Buffer address */
	#else
	__fec32 cbd_bufaddr;	/* Buffer address */
	#endif
} __attribute__((packed));

/*
* Advanced buffer descriptor format, for more information see the Nitrogen8M
* user manual.
*/
struct bufdesc_ex {
	struct bufdesc desc;
	__fec32 cbd_esc;
	__fec32 cbd_prot;
	__fec32 cbd_bdu;
	__fec32 ts;
	__fec16 res0[4];
};


/* -----------------------------------------------------------------------------
* Descriptor Ring Definition
* --------------------------------------------------------------------------- */

/*
* A descriptor ring consists of a fixed number of buffer descriptors. We need
* to enforce the limit in the code.
*/
struct descring {
  struct bufdesc_ex elements[DESCRING_ELEMENTS_N];
};

#endif

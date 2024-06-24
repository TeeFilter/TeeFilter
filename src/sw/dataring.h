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

#ifndef DATARING_H
#define	DATARING_H

#include <stdint.h>

/* -----------------------------------------------------------------------------
* Definitions for the datarings and their size.
* --------------------------------------------------------------------------- */

// 2048 * 512 * 3 = 3145728 = 3072 KiB = 3 MiB -> We allocate 4MiB for 3 TX rings
// 2048 * 512 * 3 = 3145728 = 3072 KiB = 3 MiB -> We allocate 4MiB for 3 RX rings
// We allocate 8MiB for 6 rings
// 1 MiB = 0x100000 B
// 8 MiB = 0x800000 B

// For each queue, we keep a data ring where the payloads are copied to before
// the descriptors are sent to the NIC (or vice versa). We need to copy the data
// in order to prevent time-of-check-time-of-use race conditions that manipulate
// the payload after the security checks in the secure world.

#define DATARING_BASE 0xA0400000
// #define DATARING_LIMIT 0xA0C00000

#define DATARING_ELEMENT_SIZE_BYTES 2048
#define DATATING_ELEMENTS_PER_QUEUE 512
#define DATARING_SIZE_PER_QUEUE_BYTES DATARING_ELEMENT_SIZE_BYTES * DATATING_ELEMENTS_PER_QUEUE

#define DATARING_RECEIVE_0_OFFSET 0 * DATARING_SIZE_PER_QUEUE_BYTES
#define DATARING_RECEIVE_1_OFFSET 1 * DATARING_SIZE_PER_QUEUE_BYTES
#define DATARING_RECEIVE_2_OFFSET 2 * DATARING_SIZE_PER_QUEUE_BYTES

#define DATARING_TRANSMIT_0_OFFSET 3 * DATARING_SIZE_PER_QUEUE_BYTES
#define DATARING_TRANSMIT_1_OFFSET 4 * DATARING_SIZE_PER_QUEUE_BYTES
#define DATARING_TRANSMIT_2_OFFSET 5 * DATARING_SIZE_PER_QUEUE_BYTES

#define DATARING_ELEMENT_SIZE_BYTES 2048
#define DATARING_ELEMENTS_N 512

/* -----------------------------------------------------------------------------
* Element Definition.
* --------------------------------------------------------------------------- */

/*
* An element in a dataring has a maximum size of 2048. We need to enforce the
* size limit in the code.
*/
struct element {
  uint8_t data[DATARING_ELEMENT_SIZE_BYTES];
};

/*
* A dataring contains of a fixed number of elements. We need to enforce the
* fixed limit in the code.
*/
struct dataring {
  struct element elements[DATARING_ELEMENTS_N];
};

#endif

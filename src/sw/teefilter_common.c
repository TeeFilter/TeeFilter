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

#include <stdint.h>
#include <endian.h>
#include <arch_helpers.h>

#include "teefilter_common.h"

#include "plat/memcpy.h"
#include "plat/memset.h"

/* -----------------------------------------------------------------------------
* Public Interface
* --------------------------------------------------------------------------- */

void destroy(uint8_t* buffer, uint32_t size) {
  #ifdef MODEL
  memset(buffer, 0x0, size);
  #else
  memset_aarch64(buffer, 0x0, size);
  #endif
}

/*
* This function copies a buffer descriptor from src to dest and assignes a
* new address for the payload field of the buffer descriptor.
* dest, src, and new_data_addr must be checked before calling this function.
*/
#ifdef MODEL
void copy_desc(struct bufdesc_ex* dest, struct bufdesc_ex* src,
    uint8_t* new_data_addr) {
#else
void copy_desc(struct bufdesc_ex* dest, struct bufdesc_ex* src,
    uint32_t new_data_addr) {
#endif
  // It is important that the status field is set last, since this transfers
  // the ownership to the device.
	dest->cbd_esc = src->cbd_esc;
  dest->cbd_prot = src->cbd_prot;
  dest->cbd_bdu = src->cbd_bdu;
  dest->ts = src->ts;

  dest->res0[0] = src->res0[0];
  dest->res0[1] = src->res0[1];
  dest->res0[2] = src->res0[2];
  dest->res0[3] = src->res0[3];

  dest->desc.cbd_datlen = src->desc.cbd_datlen;
  #ifdef MODEL
  dest->desc.cbd_bufaddr = new_data_addr;
  #else
  dest->desc.cbd_bufaddr = htole32(new_data_addr);
  #endif

  dsb();

  // Transfer ownership
  dest->desc.cbd_sc = src->desc.cbd_sc;
}

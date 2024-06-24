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
#include <lib/mmio.h>
#include <endian.h>
#include <arch_helpers.h>

#include "teefilter_tx_common.h"
#include "dataring.h"
#include "descring.h"
#include "checks.h"
#include "state.h"

/* -----------------------------------------------------------------------------
* Helper Functions For Buffer Descriptor Handling
* --------------------------------------------------------------------------- */

uint16_t copy_desc_wo_ownership(struct bufdesc_ex* dest, struct bufdesc_ex* src) {

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
  dest->desc.cbd_bufaddr = src->desc.cbd_bufaddr;

	linux_dma_wmb();

  #ifdef MODEL
	uint16_t status = src->desc.cbd_sc;
  #else
	uint16_t status = le16toh(src->desc.cbd_sc);
  #endif
	uint16_t prev_status = status;

	status = status & ~BD_ENET_TX_READY;

  #ifdef MODEL
	dest->desc.cbd_sc = status;
  #else
	dest->desc.cbd_sc = htole16(status);
  #endif

	linux_wmb();

	return prev_status;
}

/*
* Update the data pointer of an existing buffer descriptor.
* bd and new_data need to be checked when calling this function.
*/
void update_data(struct bufdesc_ex* bd, uint8_t* new_data) {
  if(((uint64_t) new_data) > 0xFFFFFFFF) {
    ERROR("Address too large\n");
    return;
  }

  #ifdef MODEL
	bd->desc.cbd_bufaddr = (uint32_t) ((uint64_t) new_data);
  #else
	bd->desc.cbd_bufaddr = htole32((uint32_t) ((uint64_t) new_data));
  #endif
}

/*
* Transmit the ownership of a buffer descriptor to the NIC, i.e., the NIC is
* allowed to process the buffer descriptor.
* bd needs to be checked when calling this function
*/
void transmit_ownership(struct bufdesc_ex* bd) {
  #ifdef MODEL
	uint16_t status = bd->desc.cbd_sc;
  #else
	uint16_t status = le16toh(bd->desc.cbd_sc);
  #endif

	status = status | BD_ENET_TX_READY;

	linux_dma_wmb();
  #ifdef MODEL
	bd->desc.cbd_sc = status;
  #else
	bd->desc.cbd_sc = htole16(status);
  #endif
	linux_wmb();
}

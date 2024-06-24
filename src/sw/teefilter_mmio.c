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

#include "teefilter_mmio.h"

#include <platform_def.h>
#include <endian.h>
#include <lib/mmio.h>
#include <arch_helpers.h>

#include "checks.h"
#include "state.h"

// #define RECORDER
#define ENFORCE


/* -----------------------------------------------------------------------------
* Write Operation
* --------------------------------------------------------------------------- */

static void handle_tx_base_write(uint32_t queue, uint64_t address, uint32_t val) {

  if(!is_nw_ram_region(val, DESCRING_SIZE_BYTES)) {
    ERROR("handle_tx_base_write: Not a NW RAM region: %x, %d\n", val, DESCRING_SIZE_BYTES);
    return;
  }

  #ifdef MODEL
  __CPROVER_assert(is_nw_ram_region(val, DESCRING_SIZE_BYTES), "handle_tx_base_write #1");
  #endif

	INFO("Initialize the shadow ring buffer\n");
  state.nw_tx_descrings[queue] = (struct descring*) ((uint64_t) val);
  state.shadow_tx_current[queue] = 0x0;

  // It is very important that we intialize the ring buffer accordingly.
  // This is taken from the original driver.
  for(uint32_t i=0; i<DESCRING_ELEMENTS_N; i++) {
		// Set the initial values of the buffer descriptor
    struct bufdesc_ex* ele = &state.shadow_tx_descrings[queue]->elements[i];

		// Those lines are the evil of non-provability
    #ifdef MODEL
    ele->desc.cbd_bufaddr = 0x0;
    ele->desc.cbd_sc = (i == DESCRING_ELEMENTS_N-1) ? BD_SC_WRAP : 0;
    #else
    ele->desc.cbd_bufaddr = htole32(0);
    ele->desc.cbd_sc = htole16((i == DESCRING_ELEMENTS_N-1) ? BD_SC_WRAP : 0);
    #endif

		// Initially, we assume every position has a header
		state.has_header[queue][i] = true;
  }

  dsb();

  INFO("The shadow buffer is enabled for queue %d\n", queue);

	struct descring* descring = state.shadow_tx_descrings[queue];
	if(((uint64_t) descring) > 0xFFFFFFFF) {
		ERROR("Adress of descring is too big\n");
		return;
	}

  uint32_t new_val = (uint32_t) ((uint64_t) descring);
  uint32_t* ptr = (uint32_t*) address;
  *ptr = new_val;

  dsb();
}


static void handle_rx_base_write(uint32_t queue, uint64_t address, uint32_t val) {

  if(!is_nw_ram_region(val, DESCRING_SIZE_BYTES)) {
    ERROR("handle_rx_base_write: Not a NW RAM region: %x, %d\n", val, DESCRING_SIZE_BYTES);
    return;
  }

  #ifdef MODEL
  __CPROVER_assert(is_nw_ram_region(val, DESCRING_SIZE_BYTES), "handle_rx_base_write #1");
  #endif

	INFO("Initialize the shadow ring buffer\n");
  state.nw_rx_descrings[queue] = (struct descring*) ((uint64_t) val);

  // It is very important that we intialize the ring buffer accordingly.
  // This is taken from the original driver.
  for(uint32_t i=0; i<DESCRING_ELEMENTS_N; i++) {
    struct bufdesc_ex* ele = &state.shadow_rx_descrings[queue]->elements[i];
    struct element* shadowData = &state.rx_datarings[queue]->elements[i];

		if(((uint64_t) shadowData) > 0xFFFFFFFF) {
			ERROR("shadowData too large\n");
			return;
		}

    #ifdef MODEL
    ele->desc.cbd_bufaddr = shadowData;
    ele->cbd_esc = BD_ENET_RX_INT;
    #else
    ele->desc.cbd_bufaddr = htole32((uint32_t)((uint64_t) shadowData));
    ele->cbd_esc = htole32(BD_ENET_RX_INT);
    #endif

    dsb();

    uint16_t status = BD_ENET_RX_EMPTY;
    status = status | ((i == DESCRING_ELEMENTS_N-1) ? BD_SC_WRAP : 0);

    #ifdef MODEL
    ele->desc.cbd_sc = status;
    #else
    ele->desc.cbd_sc = htole16(status);
    #endif

    dsb();
  }

  dsb();

  INFO("The shadow buffer is enabled for queue %d\n", queue);

	struct descring* descring = state.shadow_rx_descrings[queue];
  uint32_t* ptr = (uint32_t*) address;
  *ptr = (uint32_t) ((uint64_t) descring);

  dsb();
}


void teefilter_write32(uint32_t val, uint64_t address) {
  if(!is_word_in_nic_mmio_space(address)) {
    ERROR("Invalid NIC MMIO address: %llx\n", address);
    return;
  }

  // There is no underflow/overflow, since we already know that address is
  // in the NIC range.
  uint64_t offset = ((uint64_t) address) - IMX_NIC_BASE;

  // First, we handle base registers
  switch (offset) {
    case ENET_TDSR0:
      handle_tx_base_write(0, address, val);
      return;
    case ENET_TDSR1:
      handle_tx_base_write(1, address, val);
      return;
    case ENET_TDSR2:
      handle_tx_base_write(2, address, val);
      return;
    case ENET_RDSR0:
      handle_rx_base_write(0, address, val);
      return;
    case ENET_RDSR1:
      handle_rx_base_write(1, address, val);
      return;
    case ENET_RDSR2:
      handle_rx_base_write(2, address, val);
      return;
  }

	// Now, we handle critical registers
  switch (offset) {
		case ENET_ECR: {
			#ifdef RECORDER
			INFO("Set register ENET_ECR to %x\n", val);
			#endif
			#ifdef ENFORCE
			if(val != 0x0 && val != 0x2 && val != 0x112 && val != 0x123 && val != 0x132) {
				ERROR("Wrong value for register ENET_ECR: %x\n", val);
        return;
			}
			#endif
      break;
		}

		case ENET_RCR: {
			#ifdef RECORDER
			INFO("Set register ENET_RCR to %x\n", val);
			#endif
			#ifdef ENFORCE
			if(val != 0x47c00064 && val != 0x47c00044 && val != 0x47c00046 && val != 0x0) {
				ERROR("Wrong value for register ENET_RCR: %x\n", val);
        return;
			}
			#endif
      break;
		}

    case ENET_TCR: {
			#ifdef RECORDER
			INFO("Set register ENET_TCR to %x\n", val);
			#endif
			#ifdef ENFORCE
			if(val != 0x0 && val != 0x4) {
				ERROR("Wrong value for register ENET_TCR: %x\n", val);
        return;
			}
			#endif
      break;
    }

    case ENET_PALR: {
			#ifdef RECORDER
			INFO("Set register ENET_PALR to %x\n", val);
			#endif
			#ifdef ENFORCE
			if(val != 0x19b809) {
				ERROR("Wrong value for register ENET_PALR: %x\n", val);
        return;
			}
			#endif
      break;
    }

    case ENET_PAUR: {
			#ifdef RECORDER
			INFO("Set register ENET_PAUR to %x\n", val);
			#endif
			#ifdef ENFORCE
			if(val != 0x96600000 && val != 0x9660ffff) {
				ERROR("Wrong value for register ENET_PAUR: %x\n", val);
        return;
			}
			#endif
      break;
    }

    case ENET_MRBR0:
    case ENET_MRBR1:
    case ENET_MRBR2: {
			#ifdef RECORDER
			INFO("Set register ENET_MRBR0/1/2 to %x\n", val);
			#endif
			#ifdef ENFORCE
      if(val != 1984) {
        ERROR("Maximum receive buffer size is not 1984: %d\n", val);
        return;
      }
			#endif
      break;
    }

		case ENET_FTRL: {
			#ifdef RECORDER
			INFO("Set register ENET_FTRL to %x\n", val);
			#endif
			#ifdef ENFORCE
			if(val != 0x7c0) {
				ERROR("Wrong value for register ENET_FTRL: %x\n", val);
        return;
			}
			#endif
      break;
		}

		case ENET_TACC: {
			#ifdef RECORDER
			INFO("Set register ENET_TACC to %x\n", val);
			#endif
			#ifdef ENFORCE
			if(val != 0x86) {
				ERROR("Wrong value for register ENET_TACC: %x\n", val);
        return;
			}
			#endif
      break;
		}

		case ENET_RACC: {
			#ifdef RECORDER
			INFO("Set register ENET_RACC to %x\n", val);
			#endif
			#ifdef ENFORCE
			if(val != 0x86) {
				ERROR("Wrong value for register ENET_RACC: %x\n", val);
        return;
			}
			#endif
      break;
		}

    case ENET_QOS: {
			#ifdef RECORDER
			INFO("Set register ENET_QOS to %x\n", val);
			#endif
			#ifdef ENFORCE
      ERROR("Should not write ENET_QOS\n");
      return;
			#endif
      break;
		}

  }

  uint32_t* ptr = (uint32_t*) address;
  *ptr = val;
}


/* -----------------------------------------------------------------------------
* Read Operation
* --------------------------------------------------------------------------- */

static uint32_t handle_rx_base_read(uint32_t queue) {
  struct descring* ring = state.nw_rx_descrings[queue];
  if(((uint64_t) ring) > 0xFFFFFFFF) {
    ERROR("Invalid address of RX ring: %p\n", ring);
    return 0x0;
  }
  return (uint32_t) ((uint64_t) ring);
}

static uint32_t handle_tx_base_read(uint32_t queue) {
  struct descring* ring = state.nw_tx_descrings[queue];
  if(((uint64_t) ring) > 0xFFFFFFFF) {
    ERROR("Invalid address of TX ring: %p\n", ring);
    return 0x0;
  }
  return (uint32_t) ((uint64_t) ring);
}

uint32_t teefilter_read32(uint64_t address) {
  if(!is_word_in_nic_mmio_space(address)) {
    ERROR("Address is not in NIC range: %llx\n", address);
    return 0;
  }

  // There is no underflow/overflow, since we already know that address is
  // in the NIC range.
  uint64_t offset = address - IMX_NIC_BASE;

  // Check if we try to read a base register
  switch (offset) {
    case ENET_TDSR0:
      return handle_tx_base_read(0);
    case ENET_TDSR1:
      return handle_tx_base_read(1);
    case ENET_TDSR2:
      return handle_tx_base_read(2);
    case ENET_RDSR0:
      return handle_rx_base_read(0);
    case ENET_RDSR1:
      return handle_rx_base_read(1);
    case ENET_RDSR2:
      return handle_rx_base_read(2);
  }

  // If we are are, we did read a NIC register but it is not a base register
  uint32_t* ptr = (uint32_t*) address;
  return *ptr;
}

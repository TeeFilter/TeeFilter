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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "teefilter_common.h"
#include "teefilter_mmio.h"
#include "teefilter_init.h"
#include "state.h"
#include "checks.h"
#include "dataring.h"


void setup() {
  __CPROVER_allocated_memory(IMX_NIC_BASE, IMX_NIC_SIZE);
}


void harness_read32() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  // TeeFilter initialization guaranteed by ATF.
  teefilter_init();

  /* -------------------------------------------------------------------------*/
  // Memory Safety
  /* -------------------------------------------------------------------------*/

  uint64_t address;
  uint32_t val = teefilter_read32(address);

  /* -------------------------------------------------------------------------*/
  // Read of non-base registers
  /* -------------------------------------------------------------------------*/

  uint64_t address1;
  __CPROVER_assume(is_word_in_nic_mmio_space(address1));
  __CPROVER_assume(address1 != IMX_NIC_BASE + ENET_TDSR0);
  __CPROVER_assume(address1 != IMX_NIC_BASE + ENET_TDSR1);
  __CPROVER_assume(address1 != IMX_NIC_BASE + ENET_TDSR2);
  __CPROVER_assume(address1 != IMX_NIC_BASE + ENET_RDSR0);
  __CPROVER_assume(address1 != IMX_NIC_BASE + ENET_RDSR1);
  __CPROVER_assume(address1 != IMX_NIC_BASE + ENET_RDSR2);

  uint32_t val1 = teefilter_read32(address1);
  uint32_t check1 = *((uint32_t*) address1);
  __CPROVER_assert(val1 == check1, "harness_read32 #1");

  /* -------------------------------------------------------------------------*/
  // Read of registers
  /* -------------------------------------------------------------------------*/

  uint64_t address2 = IMX_NIC_BASE + ENET_TDSR0;
  uint32_t val2 = teefilter_read32(address2);
  __CPROVER_assert(val2 == state.nw_tx_descrings[0], "harness_read32 #2");

  uint64_t address3 = IMX_NIC_BASE + ENET_TDSR1;
  uint32_t val3 = teefilter_read32(address3);
  __CPROVER_assert(val3 == state.nw_tx_descrings[1], "harness_read32 #3");

  uint64_t address4 = IMX_NIC_BASE + ENET_TDSR2;
  uint32_t val4 = teefilter_read32(address4);
  __CPROVER_assert(val4 == state.nw_tx_descrings[2], "harness_read32 #4");


  uint64_t address5 = IMX_NIC_BASE + ENET_RDSR0;
  uint32_t val5 = teefilter_read32(address5);
  __CPROVER_assert(val5 == state.nw_rx_descrings[0], "harness_read32 #5");

  uint64_t address6 = IMX_NIC_BASE + ENET_RDSR1;
  uint32_t val6 = teefilter_read32(address6);
  __CPROVER_assert(val6 == state.nw_rx_descrings[1], "harness_read32 #6");

  uint64_t address7 = IMX_NIC_BASE + ENET_RDSR2;
  uint32_t val7 = teefilter_read32(address7);
  __CPROVER_assert(val7 == state.nw_rx_descrings[2], "harness_read32 #7");
}


void harness_write32_memory_safety() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  // TeeFilter initialization guaranteed by ATF.
  teefilter_init();

  struct descring shadow_tx_descrings[3];
  state.shadow_tx_descrings[0] = &shadow_tx_descrings[0];
  state.shadow_tx_descrings[1] = &shadow_tx_descrings[1];
  state.shadow_tx_descrings[2] = &shadow_tx_descrings[2];

  struct descring shadow_rx_descrings[3];
  state.shadow_rx_descrings[0] = &shadow_rx_descrings[0];
  state.shadow_rx_descrings[1] = &shadow_rx_descrings[1];
  state.shadow_rx_descrings[2] = &shadow_rx_descrings[2];

  struct dataring shadow_data[3];
  state.rx_datarings[0] = &shadow_data[0];
  state.rx_datarings[1] = &shadow_data[1];
  state.rx_datarings[2] = &shadow_data[2];

  /* -------------------------------------------------------------------------*/
  // Memory Safety
  /* -------------------------------------------------------------------------*/

  uint64_t address;
  uint32_t val;

  teefilter_write32(val, address);
}


void harness_write32_regular() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  // TeeFilter initialization guaranteed by ATF.
  teefilter_init();

  struct descring shadow_tx_descrings[3];
  state.shadow_tx_descrings[0] = &shadow_tx_descrings[0];
  state.shadow_tx_descrings[1] = &shadow_tx_descrings[1];
  state.shadow_tx_descrings[2] = &shadow_tx_descrings[2];

  struct descring shadow_rx_descrings[3];
  state.shadow_rx_descrings[0] = &shadow_rx_descrings[0];
  state.shadow_rx_descrings[1] = &shadow_rx_descrings[1];
  state.shadow_rx_descrings[2] = &shadow_rx_descrings[2];

  struct dataring shadow_data[3];
  state.rx_datarings[0] = &shadow_data[0];
  state.rx_datarings[1] = &shadow_data[1];
  state.rx_datarings[2] = &shadow_data[2];

  /* -------------------------------------------------------------------------*/
  // Regular Register
  /* -------------------------------------------------------------------------*/

  uint64_t address;
  uint32_t val;

  // NIC register
  __CPROVER_assume(is_word_in_nic_mmio_space(address));

  // not a base register
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_TDSR0);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_TDSR1);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_TDSR2);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_RDSR0);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_RDSR1);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_RDSR2);

  // not a critical register
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_ECR);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_RCR);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_TCR);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_PALR);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_PAUR);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_MRBR0);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_MRBR1);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_MRBR2);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_FTRL);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_TACC);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_RACC);
  __CPROVER_assume(address != IMX_NIC_BASE + ENET_QOS);

  teefilter_write32(val, address);

  uint32_t check = *((uint32_t*) address);
  __CPROVER_assert(val == check, "harness_write32_regular #1");
}


void harness_write32_base() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  // TeeFilter initialization guaranteed by ATF.
  teefilter_init();

  struct descring shadow_tx_descrings[3];
  state.shadow_tx_descrings[0] = &shadow_tx_descrings[0];
  state.shadow_tx_descrings[1] = &shadow_tx_descrings[1];
  state.shadow_tx_descrings[2] = &shadow_tx_descrings[2];

  struct descring shadow_rx_descrings[3];
  state.shadow_rx_descrings[0] = &shadow_rx_descrings[0];
  state.shadow_rx_descrings[1] = &shadow_rx_descrings[1];
  state.shadow_rx_descrings[2] = &shadow_rx_descrings[2];

  struct dataring shadow_data[3];
  state.rx_datarings[0] = &shadow_data[0];
  state.rx_datarings[1] = &shadow_data[1];
  state.rx_datarings[2] = &shadow_data[2];

  /* -------------------------------------------------------------------------*/
  // Base Register
  /* -------------------------------------------------------------------------*/

  uint32_t val;
  __CPROVER_assume(is_nw_ram_region(val, DESCRING_SIZE_BYTES));

  uint64_t address1 = IMX_NIC_BASE + ENET_TDSR0;
  teefilter_write32(val, address1);
  __CPROVER_assert(state.nw_tx_descrings[0] == val, "harness_write32 #1");

  uint64_t address2 = IMX_NIC_BASE + ENET_TDSR1;
  teefilter_write32(val, address2);
  __CPROVER_assert(state.nw_tx_descrings[1] == val, "harness_write32 #2");

  uint64_t address3 = IMX_NIC_BASE + ENET_TDSR2;
  teefilter_write32(val, address3);
  __CPROVER_assert(state.nw_tx_descrings[2] == val, "harness_write32 #3");

  uint64_t address4 = IMX_NIC_BASE + ENET_RDSR0;
  teefilter_write32(val, address4);
  __CPROVER_assert(state.nw_rx_descrings[0] == val, "harness_write32 #4");

  uint64_t address5 = IMX_NIC_BASE + ENET_RDSR1;
  teefilter_write32(val, address5);
  __CPROVER_assert(state.nw_rx_descrings[1] == val, "harness_write32 #5");

  uint64_t address6 = IMX_NIC_BASE + ENET_RDSR2;
  teefilter_write32(val, address6);
  __CPROVER_assert(state.nw_rx_descrings[2] == val, "harness_write32 #6");
}


void harness_write32_critical() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  // TeeFilter initialization guaranteed by ATF.
  teefilter_init();

  struct descring shadow_tx_descrings[3];
  state.shadow_tx_descrings[0] = &shadow_tx_descrings[0];
  state.shadow_tx_descrings[1] = &shadow_tx_descrings[1];
  state.shadow_tx_descrings[2] = &shadow_tx_descrings[2];

  struct descring shadow_rx_descrings[3];
  state.shadow_rx_descrings[0] = &shadow_rx_descrings[0];
  state.shadow_rx_descrings[1] = &shadow_rx_descrings[1];
  state.shadow_rx_descrings[2] = &shadow_rx_descrings[2];

  struct dataring shadow_data[3];
  state.rx_datarings[0] = &shadow_data[0];
  state.rx_datarings[1] = &shadow_data[1];
  state.rx_datarings[2] = &shadow_data[2];

  /* -------------------------------------------------------------------------*/
  // Critical Register
  /* -------------------------------------------------------------------------*/

  {
    uint64_t address = IMX_NIC_BASE + ENET_ECR;
    uint32_t val;
    __CPROVER_assume(
        !(val != 0x0 && val != 0x2 && val != 0x112 && val != 0x123 && val != 0x132)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val_neg != 0x0 && val_neg != 0x2 && val_neg != 0x112 && val_neg != 0x123 && val_neg != 0x132
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_RCR;
    uint32_t val;
    __CPROVER_assume(
        !(val != 0x47c00064 && val != 0x47c00044 && val != 0x47c00046 && val != 0x0)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val_neg != 0x47c00064 && val_neg != 0x47c00044 && val_neg != 0x47c00046 && val_neg != 0x0
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_TCR;
    uint32_t val;
    __CPROVER_assume(
        !(val != 0x0 && val != 0x4)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val != 0x0 && val != 0x4
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_PALR;
    uint32_t val;
    __CPROVER_assume(
        !(val != 0x19b809)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val != 0x19b809
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_PAUR;
    uint32_t val;
    __CPROVER_assume(
        !(val != 0x96600000 && val != 0x9660ffff)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val != 0x96600000 && val != 0x9660ffff
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_MRBR0;
    uint32_t val;
    __CPROVER_assume(
        !(val != 1984)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val_neg != 1984
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_MRBR1;
    uint32_t val;
    __CPROVER_assume(
        !(val != 1984)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val_neg != 1984
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_MRBR2;
    uint32_t val;
    __CPROVER_assume(
        !(val != 1984)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val_neg != 1984
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_FTRL;
    uint32_t val;
    __CPROVER_assume(
        !(val != 0x7c0)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val_neg != 0x7c0
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_TACC;
    uint32_t val;
    __CPROVER_assume(
        !(val != 0x86)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val_neg != 0x86
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_RACC;
    uint32_t val;
    __CPROVER_assume(
        !(val != 0x86)
    );
    teefilter_write32(val, address);
    __CPROVER_assert( *((uint32_t*) address) == val , "teefilter_write32 #1");

    uint32_t val_neg;
    __CPROVER_assume(
        val_neg != 0x86
    );
    teefilter_write32(val_neg, address);
    __CPROVER_assert( *((uint32_t*) address) != val_neg , "teefilter_write32 #2");
  }

  {
    uint64_t address = IMX_NIC_BASE + ENET_QOS;
    uint32_t val;
    uint32_t val2;
    __CPROVER_assume(
      val != val2
    );
    *((uint32_t*) address) = val2;

    teefilter_write32(val, address);
    __CPROVER_assert(*((uint32_t*) address) != val , "teefilter_write32 #1");
  }
}

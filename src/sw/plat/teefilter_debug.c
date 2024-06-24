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

#include "teefilter_debug.h"

#include <lib/mmio.h>
#include <arch_helpers.h>

#include <drivers/arm/tzc380.h>


/* -----------------------------------------------------------------------------
* Public Interface
* --------------------------------------------------------------------------- */

/*
* We assign the NIC to the SW during the runtime of the kernel (during boot).
* This way we do not need to adjust U-Boot as well, which also configures the
* NIC, and, thus, would trap. This is not secure for a productive setup.
*/
void prot_nic() {
  INFO("Restricting access to NIC\n");
  dsb();
  mmio_write_32(IMX_CSU_BASE + 47 * 4, 0x00ff0033); // disallow access from NW
  // mmio_write_32(IMX_CSU_BASE + 47 * 4, 0x00ff00ff); // allow access from NW
  dsb();
  INFO("Restricting access to NIC done\n");

  NOTICE("Starting to configure the ring buffer memory\n");
  tzc380_init(IMX_TZASC_BASE);

  NOTICE("Starting to configure the ring buffer for the buffer descriptors\n");
  // Ring Buffer is from 0xA0200000 to 0xA0400000.
  tzc380_configure_region(2, 0x60200000, TZC_ATTR_REGION_SIZE(TZC_REGION_SIZE_2M) |
        TZC_ATTR_REGION_EN_MASK | TZC_ATTR_SP_S_RW);
  NOTICE("Finished to configure the ring buffer for the buffer descriptors\n");

  // Data Ring is from 0xA0400000 to 0xA0C00000.
  NOTICE("Starting to configure the data ring memory\n");
  tzc380_configure_region(3, 0x60400000, TZC_ATTR_REGION_SIZE(TZC_REGION_SIZE_8M) |
        TZC_ATTR_REGION_EN_MASK | TZC_ATTR_SP_S_RW);
  NOTICE("Finished to configure the data ring memory\n");

  dsb();
}

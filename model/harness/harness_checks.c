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
#include <lib/utils_def.h>

#include "checks.h"
#include "platform_def.h"


void harness_is_nw_ram_region() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  uint64_t address;
  uint32_t size;

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  bool result = is_nw_ram_region(address, size);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  // For a valid address/size pair that does not overflow
  uint64_t x1 = address;
  if (address > UINT64_MAX - size) {
    __CPROVER_assert(result == false, "harness_checks #1");
    return;
  }
  uint64_t x2 = address + size;

  // If intersection with SW, we must return false
  uint64_t z1 = PROT_SECURE_MEM_AREA_START;
  uint64_t z2 = PROT_SECURE_MEM_AREA_STOP-1; // ranges are inclusive

  // Now, ensure that we do not cross SW RAM
  bool sw = x1 <= z2 && z1 <= x2;

  __CPROVER_assert(sw ==> is_nw_ram_region(address, size) == false, "harness_checks #2");

  uint64_t y1 = IMX_DRAM_BASE;
  uint64_t y2 = IMX_DRAM_BASE + (uint64_t) IMX_DRAM_SIZE;
  bool ram = x1 <= y2 && y1 <= x2;

  __CPROVER_assert(ram && !sw ==> is_nw_ram_region(address, size) == true, "harness_checks #3");

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


void harness_is_word_in_nic_mmio_space() {
  // First case: Address smaller than NIC region
  uint64_t address;
  __CPROVER_assume(address < IMX_NIC_BASE);
  __CPROVER_assert(is_word_in_nic_mmio_space(address) == false, "below");

  // Second case: Address in NIC region
  uint64_t address2;
  __CPROVER_assume(address2 >= IMX_NIC_BASE);
  __CPROVER_assume(address2 < IMX_NIC_BASE + (uint64_t) IMX_NIC_SIZE);
  __CPROVER_assume(address2 % 4 == 0);
  __CPROVER_assert(is_word_in_nic_mmio_space(address2) == true, "in");

  // Third case: Address above secure region
  uint64_t address3;
  __CPROVER_assume(address3 >= IMX_NIC_BASE + (uint64_t) IMX_NIC_SIZE);
  __CPROVER_assert(is_word_in_nic_mmio_space(address3) == false, "after");
}

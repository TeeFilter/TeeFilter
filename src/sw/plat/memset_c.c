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

#include <arch_helpers.h>

#include "memset.h"


/* every pointer passed and len is assumed to be checked by caller */
extern void* __memset_aarch64(void* dst, int c, size_t len);

// We need this code here in order to allow unaligned memory accessed that
// happen during the execution of the optimized __memcpy_aarch64 function.
// https://stackoverflow.com/questions/69011672/armv8-unaligned-ldr-in-el3-causes-exception-data-abort
// https://developer.arm.com/documentation/ddi0595/2021-06/AArch64-Registers/SCTLR-EL3--System-Control-Register--EL3-?lang=en#fieldset_0-1_1
// We still do not know exactly why we cannot restore the "A" bit after the
// operation has finished. Still, it works this way.
void* memset_aarch64(void* dst, int c, size_t len) {
  write_sctlr_el3(read_sctlr_el3() & ~SCTLR_A_BIT);

  void* ret = __memset_aarch64(dst, c, len);
  return ret;
}

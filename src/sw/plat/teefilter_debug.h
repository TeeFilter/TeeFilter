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

#ifndef TEEFILTER_DEBUG_H
#define TEEFILTER_DEBUG_H

#include <stdint.h>

#include "../descring.h"


/* -----------------------------------------------------------------------------
* Public Interface
* --------------------------------------------------------------------------- */

/*
* We assign the NIC to the SW during the runtime of the kernel (during boot).
* This way we do not need to adjust U-Boot as well, which also configures the
* NIC, and, thus, would trap. This is not secure for a productive setup.
*/
void prot_nic();

#endif

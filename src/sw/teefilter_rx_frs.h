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

#ifndef TEEFILTER_RX_FRS_H
#define	TEEFILTER_RX_FRS_H

#include <stdint.h>

#include "descring.h"
#include "dataring.h"

/* -----------------------------------------------------------------------------
* Public Interface
* --------------------------------------------------------------------------- */

void rx_frs(uint32_t queue, uint32_t current, uint32_t budget);

#endif /* TEEFILTER_RX_FRS_H */

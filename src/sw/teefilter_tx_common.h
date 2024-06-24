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

#ifndef TEEFILTER_TX_COMMON_H
#define TEEFILTER_TX_COMMON_H

#include "descring.h"

/* -----------------------------------------------------------------------------
* Public Interface
* --------------------------------------------------------------------------- */

uint16_t copy_desc_wo_ownership(struct bufdesc_ex* dest, struct bufdesc_ex* src);

void update_data(struct bufdesc_ex* bd, uint8_t* new_data);

void transmit_ownership(struct bufdesc_ex* bd);

#endif /* TEEFILTER_TX_COMMON_H */

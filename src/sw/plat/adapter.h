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

#ifndef ADAPTER_H
#define ADAPTER_H

#include <stdint.h>

/* -----------------------------------------------------------------------------
* SMC Protocol Definition
* --------------------------------------------------------------------------- */

#define FUNCID_PROT_NIC_RAW UL(19)
#define FUNCID_WRITE_32_RAW UL(20)
#define FUNCID_READ_32_RAW UL(21)
#define FUNCID_TX_TOS_RAW UL(22)
#define FUNCID_TX_FRS_RAW UL(23)
#define FUNCID_RX_FRS_RAW UL(24)
#define FUNCID_RX_TOS_RAW UL(25)
#define FUNCID_UPDATE_NONCE_RAW UL(26)
#define FUNCID_UPDATE_SUBMIT_RAW UL(27)

#endif

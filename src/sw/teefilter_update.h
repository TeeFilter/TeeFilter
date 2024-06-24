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

#ifndef TEEFILTER_UPDATE_H
#define	TEEFILTER_UPDATE_H

#include <stdint.h>
#include <stdbool.h>

#include "state.h"

/* -------------------------------------------------------------------------- */
/* Opcodes                                                                    */
/* -------------------------------------------------------------------------- */
typedef uint32_t MSG_Opcode;

#define MSG_UPDATE_SUBMIT 10

/* -----------------------------------------------------------------------------
* Message Definitions
* --------------------------------------------------------------------------- */

#define RULE_SIZE 1024

struct Update {
  MSG_Opcode  opcode;
  uint64_t nonce;
  uint32_t length;
  uint8_t rule[RULE_SIZE];
	uint8_t     signature[64];
} __attribute__((packed, aligned(4)));

#define SIGNED_SIZE  sizeof(MSG_Opcode) + sizeof(uint64_t) + sizeof(uint32_t) + 1024 * sizeof(uint8_t)

/* -----------------------------------------------------------------------------
* Public Interface
* --------------------------------------------------------------------------- */

void update_get_nonce(uint64_t* nonce);
bool update_submit(struct bpf* bpf, uint64_t address, uint64_t current_nonce);

#endif /* TEEFILTER_UPDATE_H */

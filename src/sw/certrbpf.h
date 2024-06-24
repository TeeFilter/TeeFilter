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

#ifndef CERTBPF_H
#define CERTBPF_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#include "state.h"

// stack size for the VM.
#define BPF_STACK_SIZE 512

// maximum number of instructions the interpreter executes before timing out
#define BPF_FUEL 2048

// virtual memory map for the program
#define BPF_STACK_ADDR  (0x100000)
#define BPF_PACKET_ADDR (0x200000)


/* -----------------------------------------------------------------------------
* Public Interface Declaration
* --------------------------------------------------------------------------- */

void certrbpf_init(struct bpf* bpf);

bool certrbpf_run(struct bpf* bpf, uint8_t* packet, size_t packet_len,
    uint32_t direction);

void certrbpf_update(struct bpf* bpf, uint8_t* rule, uint32_t length);

#endif

#!/usr/bin/env python3

################################################################################
#  Copyright (C) 2022-2024 Jonas Röckl <joroec@gmx.net>
#  This program is free software; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License
#  as published by the Free Software Foundation; either version 2
#  of the License, or (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; If not, see <http://www.gnu.org/licenses/>.
################################################################################

# Opcode 0x18 (load double word immediate) is the only BPF instruction that
# is 16 byte long. CertrBPF expects the second "pseudo instruction" to have
# opcode 0x10 instead of 0x0 as defined in the specification.
# https://www.kernel.org/doc/html/latest/bpf/instruction-set.html#instruction-encoding
# For this reason, we replace 0x0 in the pseudo-instruction with 0x10.

import sys

def patch_text(text):
    text = bytearray(text)
    # iterate over every opcode (= start byte of a 8-byte instruction)
    for i in range(0, len(text), 8):
        opcode = text[i]
        # if the opcode is LD_DW
        if opcode == 0x18:
            # patch the next opcode to 0x10
            text[i+8] = 0x10
            # and copy the src and dst register
            text[i+9] = text[i+1]

    # force the code to end in an exit instruction (0x95)
    # the compiler might place the exit instruction at a different location
    # but the CertrBPF verifier expects it to always be at the end
    if len(text) >= 8 and text[-8] != 0x95:
        text += b"\x95" + b"\x00" * 7

    return bytes(text)

if len(sys.argv) != 2:
    print(f"usage: {sys.argv[0]} <file.bpf>")
    exit(1)

with open(sys.argv[1], "rb") as f:
   text = f.read()

patched = patch_text(text)

with open(sys.argv[1], "wb") as f:
    f.write(patched)

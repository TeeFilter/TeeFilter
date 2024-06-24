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

# target little-endian ebpf
CFLAGS = -target bpfel -Wall -Wno-unused-function -I/usr/include/x86_64-linux-gnu/ -c
CC = clang

ifeq ($(DEBUG),1)
CFLAGS += -O0
else
CFLAGS += -O3
endif

INSTALL_FILE = ../sw/certrbpf_program.h

OBJDUMP = llvm-objdump

.PHONY: all install disam clean

all: filter.bpf

# install the compiled filter program in the current version of teefilter
install: filter.bpf
	xxd -i filter.bpf | sed -e "s/filter_bpf/bpf_program/g" > $(INSTALL_FILE)

# disassemble the filter program
disasm: filter.o
	$(OBJDUMP) -d filter.o

clean:
	rm -f filter.bpf filter.o

%.o: %.c
	$(CC) $(CFLAGS) -o $@ $<

%.bpf: %.o
	llvm-objcopy -O binary --only-section=.text $< $@
	./patch.py $@

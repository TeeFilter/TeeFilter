#!/usr/bin/env python3

# ##############################################################################
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
# ##############################################################################

import sys
import subprocess
import re
import pty

################################################################################

CBMC = "/usr/local/bin/cbmc"
GOTO = "/usr/local/bin/goto-cc"
INSTRUMENT = "/usr/local/bin/goto-instrument"

# This is valid, since the NW drivers sets the NAPI_POLL_WEIGHT to 64.
# We enforce the budget in SW code.
UPPER_BOUND_BUDGET = 65

# This is valid, since we build chunks of 64 elements if there are many multiple
# frames for tranmission. We build two iterators. An upper layer that iterates
# over the chunks and a lower layer that iterates over the buffer descriptors.
# Then, we prove them individually. This way, we are able to verify them.
# Without that, we would end up in a state explosion.
UPPER_BOUND_TX_CHUNK = 65

# This is valid since the NW drivers uses these maximum values. We enforce the
# values in the SW code.
UPPER_BOUND_RX_DATA = 1521
UPPER_BOUND_TX_DATA = 1521

################################################################################

# build directory for temporary files
BUILD = "build"

# source directory for the source code of the system
SRCDIR = "../src/sw"

# directory that includes the harnesses for the source code
HARNESSDIR = "harness"

################################################################################

# flags for the compiler, #define MODEL
CXXFLAGS = "-DMODEL -I mocks -I mocks/arch/aarch64 -I mocks/lib/libc \
	-I mocks/lib/libc/aarch64 \
	-I ../src/sw \
	-I ../dep/tfa/plat/imx/common/include		\
	-I ../dep/tfa/plat/imx/imx8m/include		\
	-I ../dep/tfa/plat/imx/imx8m/imx8mq/include"

# flags for cmbc
CBMCFLAGS = "--arch arm64 \
		--trace \
		--slice-formula \
        --havoc-undefined-functions \
		--nondet-static"

Z3 = "--z3"

GOTOFLAGS = "" # noting to add here so far

INSTRUMENTFLAGS = "--bounds-check \
	--pointer-check              \
	--memory-leak-check          \
	--memory-cleanup-check       \
	--div-by-zero-check          \
	--signed-overflow-check      \
	--unsigned-overflow-check    \
	--pointer-overflow-check     \
	--conversion-check           \
	--undefined-shift-check      \
	--float-overflow-check       \
	--nan-check                  \
	--enum-range-check           \
	--pointer-primitive-check"

################################################################################

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

################################################################################

def run(command) -> int:
    """
    raises CalledProcessError if subprocess does not terminate with exit status
    of zero.
    """
    command = " ".join(command.splitlines())
    command = re.sub(' +', ' ', command) # replace multiple spaces
    command = re.sub('\t+', ' ', command) # replace tabs
    command = command.strip() # remove trailing and leading whitespace
    print(f"{bcolors.OKBLUE}Running command: {command}{bcolors.ENDC}")
    command = command.split() # split to tokens again

    rc = pty.spawn(command)
    if(rc != 0):
        raise subprocess.CalledProcessError(rc, command)

    print("")
    return rc

################################################################################

def is_nw_ram_region():
    name = "is_nw_ram_region"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_checks.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def rx_frs_frame_handler_negative():
    name = "rx_frs_frame_handler_negative"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_rx_frs.c
            {SRCDIR}/teefilter_rx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/checks.c
            {SRCDIR}/certrbpf.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
            --unwindset harness_rx_frs_frame_handler_negative.0:{UPPER_BOUND_RX_DATA}
    """)

################################################################################

def rx_frs_frame_handler_positive():
    name = "rx_frs_frame_handler_positive"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_rx_frs.c
            {SRCDIR}/teefilter_rx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/checks.c
            {SRCDIR}/certrbpf.c
            --function harness_{name}
		    -DMODEL_ASSUME_POSITIVE_VERDICT
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
            --unwindset memcmp.0:{UPPER_BOUND_RX_DATA}
    """)

################################################################################

def rx_frs_bd_handler_positive():
    name = "rx_frs_bd_handler_positive"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_rx_frs.c
            {SRCDIR}/teefilter_rx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def rx_frs_bd_handler_negative():
    name = "rx_frs_bd_handler_negative"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_rx_frs.c
            {SRCDIR}/teefilter_rx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def rx_frs_iterator():
    name = "rx_frs_iterator"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_rx_frs.c
            {SRCDIR}/teefilter_rx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_SKIP_SHORTCUT
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset rx_frs_iterator.0:{UPPER_BOUND_BUDGET}
			--unwindset harness_rx_frs_iterator.0:{UPPER_BOUND_BUDGET}
    """)

################################################################################

def rx_frs():
    name = "rx_frs"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_rx_frs.c
            {SRCDIR}/teefilter_rx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def rx_tos_bd_handler():
    name = "rx_tos_bd_handler"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_rx_tos.c
            {SRCDIR}/teefilter_rx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def rx_tos_iterator():
    name = "rx_tos_iterator"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_rx_tos.c
            {SRCDIR}/teefilter_rx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_SKIP_SHORTCUT
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset rx_tos_iterator.0:{UPPER_BOUND_BUDGET}
			--unwindset harness_rx_tos_iterator.0:{UPPER_BOUND_BUDGET}
    """)

################################################################################

def rx_tos():
    name = "rx_tos"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_rx_tos.c
            {SRCDIR}/teefilter_rx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def tx_tos_frame_handler_negative():
    name = "tx_tos_frame_handler_negative"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_tos.c
            {SRCDIR}/teefilter_tx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            {SRCDIR}/certrbpf.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def tx_tos_frame_handler_positive():
    name = "tx_tos_frame_handler_positive"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_tos.c
            {SRCDIR}/teefilter_tx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            {SRCDIR}/certrbpf.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_ASSUME_POSITIVE_VERDICT
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
            --unwindset memcmp.0:{UPPER_BOUND_TX_DATA}
    """)

################################################################################

def tx_tos_bd_handler_positive():
    name = "tx_tos_bd_handler_positive"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_tos.c
            {SRCDIR}/teefilter_tx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def tx_tos_bd_handler_positive():
    name = "tx_tos_bd_handler_positive"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_tos.c
            {SRCDIR}/teefilter_tx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def tx_tos_bd_handler_negative():
    name = "tx_tos_bd_handler_negative"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_tos.c
            {SRCDIR}/teefilter_tx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def tx_tos_iterator2():
    name = "tx_tos_iterator2"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_tos.c
            {SRCDIR}/teefilter_tx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_SKIP_SHORTCUT
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset tx_tos_iterator2.0:{UPPER_BOUND_TX_CHUNK}
			--unwindset harness_tx_tos_iterator2.0:{UPPER_BOUND_TX_CHUNK}
    """)

################################################################################

def tx_tos_iterator():
    name = "tx_tos_iterator"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_tos.c
            {SRCDIR}/teefilter_tx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_SKIP_SHORTCUT
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset tx_tos_iterator.0:9
			--unwindset harness_tx_tos_iterator.0:9
    """)

################################################################################

def tx_tos():
    name = "tx_tos"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_tos.c
            {SRCDIR}/teefilter_tx_tos.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def tx_frs_bd_handler():
    name = "tx_frs_bd_handler"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_frs.c
            {SRCDIR}/teefilter_tx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def tx_frs_iterator2():
    name = "tx_frs_iterator2"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_frs.c
            {SRCDIR}/teefilter_tx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_SKIP_SHORTCUT
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset tx_frs_iterator2.0:{UPPER_BOUND_TX_CHUNK}
			--unwindset harness_tx_frs_iterator2.0:{UPPER_BOUND_TX_CHUNK}
    """)

################################################################################

def tx_frs_iterator():
    name = "tx_frs_iterator"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_frs.c
            {SRCDIR}/teefilter_tx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_SKIP_SHORTCUT
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset tx_frs_iterator.0:9
			--unwindset harness_tx_frs_iterator.0:9
    """)

################################################################################

def tx_frs():
    name = "tx_frs"

    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
 		    {HARNESSDIR}/harness_teefilter_tx_frs.c
            {SRCDIR}/teefilter_tx_frs.c
            {SRCDIR}/teefilter_common.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/teefilter_tx_common.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def is_word_in_nic_mmio_space():
    name = "is_word_in_nic_mmio_space"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_checks.c
            {SRCDIR}/checks.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def read32():
    name = "read32"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_mmio.c
            {SRCDIR}/teefilter_mmio.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def write32_memory_safety():
    name = "write32_memory_safety"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_mmio.c
            {SRCDIR}/teefilter_mmio.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset handle_tx_base_write.2:513
			--unwindset handle_rx_base_write.3:513
    """)

################################################################################

def write32_regular():
    name = "write32_regular"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_mmio.c
            {SRCDIR}/teefilter_mmio.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset handle_tx_base_write.2:513
			--unwindset handle_rx_base_write.3:513
    """)

################################################################################

def write32_base():
    name = "write32_base"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_mmio.c
            {SRCDIR}/teefilter_mmio.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset handle_tx_base_write.2:513
			--unwindset handle_rx_base_write.3:513
    """)

################################################################################

def write32_critical():
    name = "write32_critical"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_mmio.c
            {SRCDIR}/teefilter_mmio.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
			--unwindset handle_tx_base_write.2:513
			--unwindset handle_rx_base_write.3:513
    """)

################################################################################

def update_get_nonce():
    name = "update_get_nonce"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_update.c
            {SRCDIR}/teefilter_update.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def update_submit_safety():
    name = "update_submit_safety"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_update.c
            {SRCDIR}/teefilter_update.c
            {SRCDIR}/certrbpf.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def update_submit_negative():
    name = "update_submit_negative"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_update.c
            {SRCDIR}/teefilter_update.c
            {SRCDIR}/certrbpf.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_SKIP_VERIFICATION
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def update_submit_negative2():
    name = "update_submit_negative2"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_update.c
            {SRCDIR}/teefilter_update.c
            {SRCDIR}/certrbpf.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_ASSUME_FAILED_VERIFICATION
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def update_submit_positive():
    name = "update_submit_positive"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_update.c
            {SRCDIR}/teefilter_update.c
            {SRCDIR}/certrbpf.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
			-DMODEL_SKIP_VERIFICATION
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

def init():
    name = "teefilter_init"
    run(f"""
        {GOTO} {GOTOFLAGS} {CXXFLAGS}
            {HARNESSDIR}/harness_teefilter_init.c
            {SRCDIR}/teefilter_init.c
            {SRCDIR}/checks.c
            {SRCDIR}/state.c
            --function harness_{name}
            -o {BUILD}/{name}.goto1
    """)

    run(f"""
        {INSTRUMENT} {INSTRUMENTFLAGS}
            {BUILD}/{name}.goto1
            {BUILD}/{name}.goto2
    """)

    run(f"""
        {CBMC} {CBMCFLAGS} {Z3}
            {BUILD}/{name}.goto2
    """)

################################################################################

TARGETS = [
    is_nw_ram_region,
	is_word_in_nic_mmio_space,

	rx_frs_frame_handler_positive,
	rx_frs_frame_handler_negative,
	rx_frs_bd_handler_positive,
	rx_frs_bd_handler_negative,
	rx_frs_iterator,
	rx_frs,

	rx_tos_bd_handler,
	rx_tos_iterator,
	rx_tos,

	tx_tos_frame_handler_positive,
	tx_tos_frame_handler_negative,
	tx_tos_bd_handler_positive,
	tx_tos_bd_handler_negative,
	tx_tos_iterator2,
	tx_tos_iterator,
	tx_tos,

	tx_frs_bd_handler,
	tx_frs_iterator2,
	tx_frs_iterator,
	tx_frs,

	read32,
	write32_memory_safety,
	write32_regular,
	write32_base,
	write32_critical,

	update_get_nonce,
	update_submit_negative,
	update_submit_negative2,
	update_submit_positive,
	update_submit_safety,

	init,
]

def main() -> int:
    if len(sys.argv) == 2:
        input = sys.argv[1]
        for target in TARGETS:
            if target.__name__ == input.strip():
                print(f"{bcolors.OKBLUE}{bcolors.BOLD}---------------- {target.__name__} ----------------{bcolors.ENDC}")
                target()

    else:
        for target in TARGETS:
            print(f"{bcolors.OKBLUE}{bcolors.BOLD}---------------- {target.__name__} ----------------{bcolors.ENDC}")
            target()

################################################################################

if __name__ == '__main__':
    sys.exit(main())

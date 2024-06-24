# TeeFilter

This repository contains the implementation of TeeFilter.
We implement TeeFilter on a Boundary Devices Nitrogen8M development board.
This repository contains a development environment for ARMv8-A system software development with the board.
The repository contains everything required to assemble an SD card image that can be flashed onto the Nitrogen8M.

In particular, this is:
  * Trusted Firmware A (TFA)
  * U-Boot boot loader
  * Linux kernel
  * Small BusyBox root file system

Every component (including the cross-compiler) is downloaded and built from its source.

## Warning

This is a prototypical implementation of TeeFilter's concepts.
It is not ready for use in production environments.
This is, for example, due to the exemplary implementation of a filtering function that is responsible for deciding which traffic is allowed and which is not.
In a real-world setup, a manufacturer is expected to provide a filtering function.

## Directory Structure

* `dep/`: Contains the main dependencies necessary to compile the resulting binary that can be flashed onto the Nitrogen8M development board.
  * `dep/buildroot`: A customized fork (origin revision `b5037ecffd5d42771ece111a220e011fec547764`) of the Buildroot framework that is responsible for retrieving, compiling, and assembling the resulting image that is flashed onto the Nitrogen8M development board. More information on Buildroot at https://buildroot.org/.
  * `dep/linux`: A customized fork (origin revision `950d5f1badc48d274efa9b7639c96dfd614c08b4`) of the I.MX Linux kernel. More information at https://github.com/boundarydevices/linux.
  * `dep/tfa`: A customized fork (origin revision `9f6114fde03ebed6ecc482989a7660adc5a41a9d`) of the I.MX ARM Trusted Firmware A. More information at https://github.com/boundarydevices/imx-atf.
  * `dep/uboot`: A customized fork (origin revision `f2c92d838665ec3e3cc8ce8865780df92877ce4e`) of I.MX U-Boot that is a boot loader commonly found in ARM systems. More information at https://github.com/boundarydevices/u-boot-imx6.

* `docker/`: Contains files for creating a uniform build environment relying on Docker images.
* `model/`: The CBMC harnesses, mock code, and verification script to run the formal verification of the memory safety and correctness.
* `src/`: Contains TeeFilter source code.
  * `src/nw`: Contains TeeFilter normal world (NW) component that is the adjustment of the Ethernet driver. It is linked to the corresponding directory in the Linux kernel.
  * `src/sw`: Contains TeeFilter secure world (SW) component that is a secure runtime service. It is linked to the corresponding directory in the ARM Trusted Firmware A. This is the **heart** of TeeFilter's code.
    * `src/sw/plat`: Contains platform-specific code that is not formally verified.
    * `src/sw/hacl`: Contains a subset of HACL*, a formally verified cryptography library [1].
    * `src/sw/certrbpf_interpreter.*` and `src/sw/certrbpf_verifier.*`: TeeFilter relies on eBPF rules to filter Ethernet frames.
    To execute eBPF rules on the device, we port CertrBPF [2, 3], a formally-verified C implementation of an eBPF virtual machine, to the secure world. Through the eBPF rules, we ensure that errors (e.g., memory corruptions) in the manufacturer-provided filtering function do not affect the security and integrity of the TeeFilter engine.
  * `src/bpf`: Contains an exemplary filtering function that is compiled to eBPF. The eBPF binary is, later on, executed from within the SW to decide if a frame is allowed to pass the filter. The filtering rule can be compiled with a default LLVM toolchain (e.g., the one shipped with Ubuntu distributions), from any supported frontend language of LLVM (e.g., C, Rust, ...).

[1]  Jean Karim Zinzindohoué, Karthikeyan Bhargavan, Jonathan Protzenko, and Benjamin Beurdouche. 2017. HACL*: A Verified Modern Cryptographic Library. In Proceedings of the 24th ACM SIGSAC Conference on Computer and Communications Security, CCS ’17. ACM, 1789–1806. https://doi.org/10.1145/3133956.3134043

[2] Yuan, Shenghao, et al. "End-to-end Mechanized Proof of an eBPF Virtual Machine for Micro-controllers." International Conference on Computer Aided Verification. Cham: Springer International Publishing, 2022. https://doi.org/10.1007/978-3-031-13188-2_15

[3] https://gitlab.inria.fr/syuan/rbpf-dx/-/tree/CAV22-AE?ref_type=heads

## Requirements

### Target Hardware

We developed TeeFilter for the Boundary Devices Nitrogen8M development board ( https://boundarydevices.com/product/nitrogen8m/ ).
It features an NXP i.MX 8MQuad Core (Cortex-A53) CPU and 2GB of RAM.
The repository contains everything required to assemble an SD card image that can be flashed onto the Nitrogen8M.
In particular, this is the Trusted Firmware A, the U-Boot boot loader, the Linux kernel, and a small BusyBox root file system.
We use the I.MX versions of the mentioned dependencies which are provided by Boundary Devices.

### Build Host

We use a Linux AMD64 host (Ubuntu 20.04 LTS) to build the image (cross compilation) that can then be flashed onto the Nitrogen8M development board.
The compilation environment is provided as a Docker image to ease the setup.
Thus, Docker is required to build the software and the build process should succeed on other Linux distributions than Ubuntu as well.
Yet, we note that we have not tested to build the image on other hosts.

## Build Process

To build the SD card image that can then be flashed onto the Boundary Devices Nitrogen8M development board, execute the following steps.
We assume that Docker is installed and the `docker` command can be used as a regular user.

Build the Docker image required for compilation:

```shell
$ cd docker/build-env
$ ./build_image.sh
$ cd ../..
```

Open up a shell in the Docker container:

```shell
$ cd docker/build-env
$ ./shell.sh
```

In the shell **in the Docker container**, execute the following commands to start
the compilation process:

```shell
$ cd src/bpf
$ make install
$ cd ../../dep/buildroot/
$ make all
```

Depending on your computing power and your network connection, the compilation process can take a considerable amount of time. On a workstation with an Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz, 32 GB DDR4 RAM, 1TB Intel NVME SSD, and Ubuntu 20.04, the compilation process takes around 30 to 45 minutes.
The output image is stored in `dep/buildroot/output/images/sdcard.img` after the compilation process has finished.
The next step is to deploy the generated file system image to the Boundary Devices Nitrogen8M development board.

## Run Instructions

To run TeeFilter, we first need to deploy it to the Boundary Device Nitrogen8M development board.

* Connect the board with a micro USB cable to your computer.
* Connect the board using a serial console to your computer.
* Use `dmesg` on the host system to find out the TTY of the serial-to-USB converter:

```
[22327.771519] usb 1-9: pl2303 converter now attached to ttyUSB0
```

* On the computer, start a serial console with `sudo screen /dev/ttyUSB0 115200`.
  Use the TTY from the previous step. `115200` is the baud rate and should always
  be this value. Nothing is shown yet.

* Check that the physical `SWI / BOOT MODE` switch on the board is in position `OFF`.
* Plug the board into the power grid. It should now print output to the serial console
  in `screen`. You need to press any key to stop the invocation of `autoboot` before
  the countdown expires. You drop into a U-Boot shell:

```
U-Boot 2020.10-52931-gc95874b8b7 (Jun 24 2021 - 14:40:21 -0700), Build: jenkins-uboot_v2020.10-116

CPU:   i.MX8MQ rev2.1 at 1000 MHz
Reset cause: POR
Model: Boundary Devices i.MX8MQ Nitrogen8M
Board: nitrogen8m
       Watchdog enabled
DRAM:  2 GiB
MMC:   FSL_SDHC: 0
Loading Environment from MMC...
OK
Display: hdmi:1920x1080M@60 (1920x1080)
In:    serial
Out:   serial
Err:   serial

 BuildInfo:
  - ATF 63a678c

Hit any key to stop autoboot:  0
=>
```

* Using the U-Boot shell, connect the eMMC device to the computer:

```
ums 0 mmc 0
```

* Find out the right device on your computer with `dmesg`. In this case, it is `sdb`:

```
[24256.299948] scsi 6:0:0:0: Direct-Access     Linux    UMS disk 0       ffff PQ: 0 ANSI: 2
[24256.300670] sd 6:0:0:0: Attached scsi generic sg1 type 0
[24256.300950] sd 6:0:0:0: [sdb] 30621696 512-byte logical blocks: (15.7 GB/14.6 GiB)
[24256.301114] sd 6:0:0:0: [sdb] Write Protect is off
[24256.301120] sd 6:0:0:0: [sdb] Mode Sense: 0f 00 00 00
[24256.301320] sd 6:0:0:0: [sdb] Write cache: enabled, read cache: enabled, doesn't support DPO or FUA
[24256.326788]  sdb: sdb1
[24256.328857] sd 6:0:0:0: [sdb] Attached SCSI removable disk
```

* Without mounting the eMMC partition to the computer, flash the new image for the eMMC card.
The following commands are **NOT** to be executed in the Docker container but directly on your host!
The Docker container, which you enter by `./src/docker/shell.sh` is only intended for providing a uniform **compilation** environment.
The deployment needs to be done directly in a shell on your host.
Check twice that the output file is correct:

```shell
$ cd dep/buildroot
$ cat output/images/sdcard.img | sudo dd of=/dev/sdb bs=1M && /bin/sync
```

* After those commands, press `Ctrl-C` in the U-Boot shell to leave the USB mode.
  You are back in the U-Boot shell:

```
=> ums 0 mmc 0
UMS: LUN 0, dev 0, hwpart 0, sector 0x0, count 0x1d34000
CTRL+C - Operation aborted
=>
```

* You still need to flash the boot loader including ARM Trusted Firmware A as those reside on another internal partition of the eMMC card of the Nitrogen8M. To do this, execute the following command in the **U-Boot shell**. **Note:** There is no spelling error! There is a trailing `u`:

```
env set uboot_defconfig nitrogen8m
run upgradeu
```

* After the boot loader is flashed, the device is reset and should boot in the
  new version of your system software.
  Reset the board by pressing the physical reset button if it is not reset automatically.

* If the board comes up again, you can log into Linux with the user `root` and no password.


More information:
* https://boundarydevices.com/just-getting-started/
* https://wiki.boundarydevices.com/index.php/Nitrogen8M_SBC


## Network Filtering Configuration

When the board now boots up, TeeFilter is up and running in the background.
For this open-source version, we set up the TeeFilter as follows.

We allow traffic to any host, **EXCEPT** the following:
* Outgoing traffic to 1.1.1.1 is blocked
* Incoming traffic from 8.8.4.4 is blocked

To test TeeFilter directly on the board:

```shell
$ ping 8.8.8.8
PING 8.8.8.8 (8.8.8.8): 56 data bytes
64 bytes from 8.8.8.8: seq=0 ttl=57 time=5.949 ms
64 bytes from 8.8.8.8: seq=1 ttl=57 time=5.404 ms
64 bytes from 8.8.8.8: seq=2 ttl=57 time=5.321 ms
^C
--- 8.8.8.8 ping statistics ---
3 packets transmitted, 3 packets received, 0% packet loss
round-trip min/avg/max = 5.321/5.558/5.949 ms

$ ping 1.1.1.1
PING 1.1.1.1 (1.1.1.1): 56 data bytes
^C
--- 1.1.1.1 ping statistics ---
4 packets transmitted, 0 packets received, 100% packet loss

$ ping 8.8.4.4
PING 8.8.4.4 (8.8.4.4): 56 data bytes
^C
--- 8.8.4.4 ping statistics ---
2 packets transmitted, 0 packets received, 100% packet loss
```

Note that this is not a whitelist approach as described in the paper but a blacklist approach.
We opted for this one because it is easier to distribute the code like this in a way that others can more easily set up a working system.
Still, the evaluation in the paper uses a whitelist approach with a network with static IPs as described.

## Filtering Rule Update

To conduct an exemplary update process of the filtering rule, execute the following command in the Linux shell on the board:

```shell
$ modprobe teefilter-updater
INFO:    Generate nonce
INFO:    Nonce: 4be446d87c50c7e3
INFO:    Received update request
INFO:    Check nonce
INFO:    Nonce valid
INFO:    Verify the Ed25519 signature
INFO:    The Ed25519 verification succeeded!
INFO:    The nonce is valid!
INFO:    Update the rule!
INFO:    Rule updated!
```

After the update is installed, TeeFilter should allow traffic to `1.1.1.1`, which was not possible previously.
Traffic to `8.8.4.4`, however, is still blocked:

```shell
$ ping 1.1.1.1
PING 1.1.1.1 (1.1.1.1): 56 data bytes
64 bytes from 1.1.1.1: seq=0 ttl=54 time=16.598 ms
64 bytes from 1.1.1.1: seq=1 ttl=54 time=5.935 ms
64 bytes from 1.1.1.1: seq=2 ttl=54 time=5.877 ms
64 bytes from 1.1.1.1: seq=3 ttl=54 time=5.955 ms
64 bytes from 1.1.1.1: seq=4 ttl=54 time=5.836 ms
64 bytes from 1.1.1.1: seq=5 ttl=54 time=5.802 ms
64 bytes from 1.1.1.1: seq=6 ttl=54 time=5.803 ms
64 bytes from 1.1.1.1: seq=7 ttl=54 time=5.851 ms
64 bytes from 1.1.1.1: seq=8 ttl=54 time=5.909 ms
64 bytes from 1.1.1.1: seq=9 ttl=54 time=5.895 ms
^C
--- 1.1.1.1 ping statistics ---
10 packets transmitted, 10 packets received, 0% packet loss
round-trip min/avg/max = 5.802/6.946/16.598 ms
$ ping 8.8.4.4
PING 8.8.4.4 (8.8.4.4): 56 data bytes
^C
--- 8.8.4.4 ping statistics ---
4 packets transmitted, 0 packets received, 100% packet loss
```

This exemplary kernel module first retrieves a nonce and then signs an update, which is installed.
Note that on a productive setup, the private key to sign an update is **not** available on the device.
Only the operator or the manufacturer has access to this key.
We assume that the operator or manufacturer uses a remote maintenance channel to connect to the device, retrieve the nonce, and create a filter update, which is then passed to TeeFilter.

## Formal Verification

We use CBMC (https://github.com/diffblue/cbmc) to verify most of TeeFilter's code for memory safety and correctness, mitigating the risk of privilege escalations to the SW by eradicating whole classes of dangerous vulnerabilities.
For every function that can be called from the NW, we verify that the function is correct and memory safe under reasonable assumptions (see the research paper).

To run the verification process, execute the following steps:

```shell
$ cd docker/model-env
$ ./build_image.sh
$ cd ../..
```

Open up a shell in the Docker container:

```shell
$ cd docker/model-env
$ ./shell.sh
```

In the shell **in the Docker container**, execute the following commands to start the proof:

```shell
$ python3 verify.py
---------------- is_nw_ram_region ----------------
Running command: /usr/local/bin/goto-cc -DMODEL -I mocks -I mocks/arch/aarch64 -I mocks/lib/libc  -I mocks/lib/libc/aarch64  -I ../src/sw  -I ../dep/tfa/plat/imx/common/include -I ../dep/tfa/plat/imx/imx8m/include -I ../dep/tfa/plat/imx/imx8m/imx8mq/include harness/harness_checks.c ../src/sw/checks.c --function harness_is_nw_ram_region -o build/is_nw_ram_region.goto1

Running command: /usr/local/bin/goto-instrument --bounds-check  --pointer-check  --memory-leak-check  --memory-cleanup-check  --div-by-zero-check  --signed-overflow-check  --unsigned-overflow-check  --pointer-overflow-check  --conversion-check  --undefined-shift-check  --float-overflow-check  --nan-check  --enum-range-check  --pointer-primitive-check build/is_nw_ram_region.goto1 build/is_nw_ram_region.goto2
Reading GOTO program from 'build/is_nw_ram_region.goto1'
Writing GOTO program to 'build/is_nw_ram_region.goto2'

...

harness/harness_teefilter_init.c function harness_teefilter_init
[harness_teefilter_init.overflow.1] line 36 arithmetic overflow on unsigned + in i + 1u: SUCCESS
[harness_teefilter_init.array_bounds.1] line 37 array 'state'.shadow_tx_current upper bound in state.shadow_tx_current[(signed long int)i]: SUCCESS
[harness_teefilter_init.assertion.1] line 37 harness_teefilter_init #1: SUCCESS
[harness_teefilter_init.overflow.3] line 40 arithmetic overflow on unsigned + in i + 1u: SUCCESS
[harness_teefilter_init.overflow.2] line 41 arithmetic overflow on unsigned + in j + 1u: SUCCESS
[harness_teefilter_init.array_bounds.2] line 42 array 'state'.has_header upper bound in state.has_header[(signed long int)i]: SUCCESS
[harness_teefilter_init.array_bounds.3] line 42 array 'state'.has_header[] upper bound in state.has_header[(signed long int)i][(signed long int)j]: SUCCESS
[harness_teefilter_init.assertion.2] line 42 harness_teefilter_init #2: SUCCESS
[harness_teefilter_init.overflow.4] line 46 arithmetic overflow on unsigned + in i + 1u: SUCCESS
[harness_teefilter_init.array_bounds.4] line 47 array 'state'.nw_tx_descrings upper bound in state.nw_tx_descrings[(signed long int)i]: SUCCESS
[harness_teefilter_init.assertion.3] line 47 harness_teefilter_init #4: SUCCESS
[harness_teefilter_init.overflow.5] line 50 arithmetic overflow on unsigned + in i + 1u: SUCCESS
[harness_teefilter_init.array_bounds.5] line 51 array 'state'.nw_rx_descrings upper bound in state.nw_rx_descrings[(signed long int)i]: SUCCESS
[harness_teefilter_init.assertion.4] line 51 harness_teefilter_init #3: SUCCESS
[harness_teefilter_init.assertion.5] line 54 harness_teefilter_init #4: SUCCESS
[harness_teefilter_init.assertion.6] line 56 harness_teefilter_init #5: SUCCESS
[harness_teefilter_init.assertion.7] line 58 harness_teefilter_init #6: SUCCESS
[harness_teefilter_init.assertion.8] line 60 harness_teefilter_init #7: SUCCESS
[harness_teefilter_init.assertion.9] line 62 harness_teefilter_init #8: SUCCESS
[harness_teefilter_init.assertion.10] line 64 harness_teefilter_init #9: SUCCESS
[harness_teefilter_init.assertion.11] line 66 harness_teefilter_init #10: SUCCESS
[harness_teefilter_init.assertion.12] line 68 harness_teefilter_init #11: SUCCESS
[harness_teefilter_init.assertion.13] line 70 harness_teefilter_init #12: SUCCESS
[harness_teefilter_init.assertion.14] line 72 harness_teefilter_init #13: SUCCESS
[harness_teefilter_init.assertion.15] line 74 harness_teefilter_init #14: SUCCESS
[harness_teefilter_init.assertion.16] line 76 harness_teefilter_init #15: SUCCESS

** 0 of 41 failed (1 iterations)
VERIFICATION SUCCESSFUL
```

For each component that is to be verified, the script contains a target.
The script terminates early if one of the proofs fail.

The directory `model/mocks` contains some required function definitions of TFA.
We do not verify TFA but assume it is secure.
The harnesses call the exported functions with (unconstrained) parameters (only restricted by the preconditions).
The verification script connects the mocks, TeeFilter's code, and the harnesses.
We can then verify that the functions are correct and memory safe as long as the preconditions hold.
The eBPF interpreter and HACL* is formally verified using deductive techniques (see paper for more information).

## License

The contents of the `docker`, `model/harness`, and `src` directories and the file `model/verify.py` are currently licensed under GNU General Public License v2.0 (GPLv2).
Copyright: Jonas Röckl <joroec@gmx.net>

The contents of the `dep` and `model/mocks` directories are licensed under the respective licenses given in the header of the files.


## Limitations

Currently, we only assign the NIC to the SW during the runtime of the kernel, i.e., during the initialization of the NIC driver.
This way we do not need to adjust U-Boot (which runs before Linux) as well, which also configures the NIC.
If we would assign the NIC to the SW right from the start of the board, access of the U-Boot Ethernet driver to NIC registers would trap to EL3, leading to another TeeFilter implementation for U-Boot, which is out of scope for this prototype.

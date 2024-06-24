#!/bin/sh
# SPDX-License-Identifier: GPL-2.0+
#
# script to generate FIT image source for i.MX8MQ boards with
# ARM Trusted Firmware and multiple device trees (given on the command line)
#
# usage: $0 <dt_name> [<dt_name> [<dt_name] ...]

[ -z "$BL31" ] && BL31="bl31.bin"
[ -z "$TEE_LOAD_ADDR" ] && TEE_LOAD_ADDR="0xfe000000"
[ -z "$ATF_LOAD_ADDR" ] && ATF_LOAD_ADDR="0x00910000"
[ -z "$BL33_LOAD_ADDR" ] && BL33_LOAD_ADDR="0x40200000"

if [ ! -f $BL31 ]; then
	echo "ERROR: BL31 file $BL31 NOT found" >&2
	exit 0
else
	echo "$BL31 size: " >&2
	ls -lct $BL31 | awk '{print $5}' >&2
fi

LOADABLES="\"atf@1\""

if [ ! -z "$BL32" ]; then
	if [ ! -f $BL32 ]; then
		echo "ERROR: BL32 file $BL32 NOT found" >&2
		exit 0
	else
		echo "Building with TEE support, make sure your $BL31 is compiled with spd. If you do not want tee, please remove CONFIG_OPTEE_FIRMWARE" >&2
		echo "$BL32 size: " >&2
		ls -lct $BL32 | awk '{print $5}' >&2
		LOADABLES="$LOADABLES, \"tee@1\""
	fi
fi

BL33="u-boot-nodtb.bin"
DEK_BLOB="dek_blob_fit_dummy.bin"

if [ ! -f $DEK_BLOB ]; then
	DEK_BLOB=/dev/null
else
	echo "Building with encrypted boot support, make sure to replace DEK Blob in final image." >&2
	LOADABLES="\"dek_blob@1\", $LOADABLES"
fi

if [ ! -f $BL33 ]; then
	echo "ERROR: $BL33 file NOT found" >&2
	exit 0
else
	echo "u-boot-nodtb.bin size: " >&2
	ls -lct u-boot-nodtb.bin | awk '{print $5}' >&2
fi

for dtname in $*
do
	echo "$dtname size: " >&2
	ls -lct $dtname | awk '{print $5}' >&2
done

cat << __HEADER_EOF
/dts-v1/;

/ {
	description = "Configuration to load ATF before U-Boot";

	images {
		uboot@1 {
			description = "U-Boot (64-bit)";
			os = "u-boot";
			data = /incbin/("$BL33");
			type = "standalone";
			arch = "arm64";
			compression = "none";
			load = <$BL33_LOAD_ADDR>;
		};
__HEADER_EOF

cnt=1
for dtname in $*
do
	cat << __FDT_IMAGE_EOF
		fdt@$cnt {
			description = "$(basename $dtname .dtb)";
			data = /incbin/("$dtname");
			type = "flat_dt";
			compression = "none";
		};
__FDT_IMAGE_EOF
cnt=$((cnt+1))
done

cat << __HEADER_EOF
		atf@1 {
			description = "ARM Trusted Firmware";
			os = "arm-trusted-firmware";
			data = /incbin/("$BL31");
			type = "firmware";
			arch = "arm64";
			compression = "none";
			load = <$ATF_LOAD_ADDR>;
			entry = <$ATF_LOAD_ADDR>;
		};
__HEADER_EOF

if [ ! -z "$BL32" ]; then
cat << __HEADER_EOF
		tee@1 {
			description = "TEE firmware";
			data = /incbin/("$BL32");
			type = "firmware";
			arch = "arm64";
			compression = "none";
			load = <$TEE_LOAD_ADDR>;
			entry = <$TEE_LOAD_ADDR>;
		};
__HEADER_EOF
fi

if [ -f $DEK_BLOB ]; then
cat << __HEADER_EOF
		dek_blob@1 {
			description = "dek_blob";
			data = /incbin/("$DEK_BLOB");
			type = "script";
			compression = "none";
			load = <$DEK_BLOB_LOAD_ADDR>;
		};
__HEADER_EOF
fi

cat << __CONF_HEADER_EOF
	};
	configurations {
		default = "config@1";

__CONF_HEADER_EOF

cnt=1
for dtname in $*
do
cat << __CONF_SECTION_EOF
		config@$cnt {
			description = "$(basename $dtname .dtb)";
			firmware = "uboot@1";
			loadables = $LOADABLES;
			fdt = "fdt@$cnt";
		};
__CONF_SECTION_EOF
cnt=$((cnt+1))
done

cat << __ITS_EOF
	};
};
__ITS_EOF

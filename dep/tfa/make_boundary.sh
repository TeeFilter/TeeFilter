#!/bin/sh
if [ -z "$UBOOT_PATH" ]; then UBOOT_PATH=~/u-boot-imx6; fi

buildatf() {
	rm -fr build*
	make PLAT=$1 BUILD_BASE=$2 SPD=$3 bl31 -j$(nproc)
	cp -v $2/$1/release/bl31.bin $UBOOT_PATH/$4
}

buildatf imx8mm build none bl31-iMX8MM.bin
buildatf imx8mn build none bl31-iMX8MQ.bin
buildatf imx8mp build none bl31-iMX8MP.bin
buildatf imx8mq build none bl31-iMX8MQ.bin
buildatf imx8mm build-optee opteed bl31-tee-iMX8MM.bin
buildatf imx8mn build-optee opteed bl31-tee-iMX8MQ.bin
buildatf imx8mp build-optee opteed bl31-tee-iMX8MP.bin
buildatf imx8mq build-optee opteed bl31-tee-iMX8MQ.bin
chmod a-x $UBOOT_PATH/bl31-*.bin

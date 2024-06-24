################################################################################
#
# updater
#
################################################################################

# Note: Buildroot does not support to build a LKM only, so we need some wrapper
# application that is build alongside the module. In this case, this is just
# a hello world application.
# More information can be retrieved at:
# https://buildroot.org/downloads/manual/manual.html#_infrastructure_for_packages_building_kernel_modules

UPDATER_VERSION = 1.0.0
UPDATER_LICENSE = GPL-2.0
UPDATER_LICENSE_FILES = COPYING

UPDATER_SITE = ../../src/nw/updater
UPDATER_SITE_METHOD = local

UPDATER_MODULE_SUBDIRS = lkm

UPDATER_INSTALL_STAGING = NO
UPDATER_INSTALL_TARGET = YES

define UPDATER_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(@D)/hello $(TARGET_DIR)/usr/bin/hello
endef

$(eval $(kernel-module))
$(eval $(cmake-package))

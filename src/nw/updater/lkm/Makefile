obj-m += teefilter-updater.o

teefilter-updater-objs+= hacl/Hacl_Curve25519_51.o hacl/Hacl_Ed25519.o hacl/Hacl_Hash.o hacl/hacllib.o updater.o

ccflags-y := -std=gnu99 -Wno-declaration-after-statement

all:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules

clean:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean

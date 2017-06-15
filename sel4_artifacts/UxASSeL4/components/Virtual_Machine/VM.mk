#
# Copyright 2016, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
# @TAG(D61_BSD)
#

CURRENT_DIR := $(dir $(abspath $(lastword ${MAKEFILE_LIST})))

Virtual_Machine_OFILES   := archive.o
Virtual_Machine_LIBS += sel4allocman elf sel4simple sel4simple-default cpio sel4arm-vmm sel4dma
#ifeq (${CONFIG_PLAT_EXYNOS5410},y)
Virtual_Machine_LIBS +=usbdrivers
#endif

include ${PWD}/tools/camkes/camkes.mk

ifeq (${CONFIG_PLAT_EXYNOS5410},y)
ifeq (${CONFIG_VM_ROOTFS_MMCBLK0P2},y)
ROOTFS := mmcblk0p2
else ifeq (${CONFIG_VM_ROOTFS_MMCBLK1P2},y)
ROOTFS := mmcblk1p2
else
$(error Unknown root filesystem)
endif

ifeq (${CONFIG_VM_VUSB},y)
DEVICE_TREE_SRC := ${CURRENT_DIR}/../../linux/linux-secure-vusb-dtb
else
DEVICE_TREE_SRC := ${CURRENT_DIR}/../../linux/linux-secure-dtb
endif

$(STAGE_DIR)/linux/linux-dtb:
	$(Q)mkdir -p $(dir $@)
	sed "s/root=\/dev\/mmcblk1p2/root=\/dev\/${ROOTFS}/g" $(DEVICE_TREE_SRC) > $@

$(STAGE_DIR)/linux/linux:
	$(Q)mkdir -p $(dir $@)
	cp ${CURRENT_DIR}/../../linux/linux $@
endif

ifeq (${CONFIG_PLAT_TK1},y)

ifeq (${CONFIG_TK1_INSECURE},y)
DEVICE_TREE_SRC := ${CURRENT_DIR}/../../linux/linux-tk1-nonsecured.dts
else
DEVICE_TREE_SRC := ${CURRENT_DIR}/../../linux/linux-tk1-secure.dts
endif

ifeq (${CONFIG_VM_TK1_INITRD_ROOTFS},y)
TK1_LINUX_BINARY := ${CURRENT_DIR}/../../linux/linux-tk1-initrd
else
TK1_LINUX_BINARY := ${CURRENT_DIR}/../../linux/linux-tk1-debian
endif

$(STAGE_DIR)/linux/linux-dtb: $(DEVICE_TREE_SRC)
	$(Q)mkdir -p $(dir $@)
	$(Q)which dtc && dtc -I dts -O dtb $(DEVICE_TREE_SRC) > $@ || \
	(echo "ERROR: dtc potentially not installed" && false)

$(STAGE_DIR)/linux/linux: $(TK1_LINUX_BINARY)
	$(Q)mkdir -p $(dir $@)
	cp $(TK1_LINUX_BINARY) $@
endif

COMPONENTS := $(STAGE_DIR)/linux/linux $(STAGE_DIR)/linux/linux-dtb

${BUILD_DIR}/src/Virtual_Machine_inst/static/archive.o: ${COMPONENTS}
	$(Q)mkdir -p $(dir $@)
	${COMMON_PATH}/files_to_obj.sh $@ _cpio_archive $^

$(vm_CFILES:%.c=%.o) $(COMPONENTS): $(srctree)/.config

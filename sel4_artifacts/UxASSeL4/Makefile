# This flag is used by encrypt/decrypt to determine where endian.h is found
# Would be nice to give it a better name
CFLAGS += -DODROID

# Start with the generated Makefile from AADL Trusted Build
include ${PWD}/apps/soi_tk1/make_template/Makefile

####### VM files
#VM_LIBS += sel4allocman elf sel4simple sel4simple-default cpio sel4arm-vmm sel4dma usbdrivers
Virtual_Machine_CFILES := $(patsubst $(SOURCE_DIR)/%,%,$(wildcard $(SOURCE_DIR)/components/Virtual_Machine/src/*.c))
Virtual_Machine_OFILES := archive.o

Virtual_Machine_HFILES := $(patsubst ${SOURCE_DIR}/%,%,$(wildcard $(SOURCE_DIR)/components/Virtual_Machine/include/*.h)) \
                 $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/include/*.h))
Virtual_Machine_LIBS += sel4allocman elf sel4simple sel4simple-default cpio sel4arm-vmm sel4dma usbdrivers

###### End VM files

###### Waypoint Additional files

Waypoint_Manager_CFILES :=  ${Waypoint_Manager_CFILES} \
	$(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/Waypoint_Manager/src/CMASI/*.c)) \
	$(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/Waypoint_Manager/src/CMASI/common/*.c))

Waypoint_Manager_HFILES :=  ${Waypoint_Manager_HFILES} \
	$(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/Waypoint_Manager/src/CMASI/*.h)) \
	$(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/Waypoint_Manager/src/CMASI/common/*.h))



###### End Waypoint files




###### UART files

uart_shim_HFILES := \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/UART_Driver/uart_shim/include/*.h)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/include/*.h))
uart_shim_CFILES := \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/UART_Driver/uart_shim/src/*.c))

###### End UART

###### Clock_Driver files


## NOTE WE DO NOT ACTUALLY NEED TO DO THIS FORWARDING

include ${PWD}/projects/DARPA-tk1/components/clkcar/clkcar.mk

###### End Clock_Driver


include ${PWD}/tools/camkes/camkes.mk

ifeq (${CONFIG_VM_TK1_INITRD_ROOTFS},y)
	DEVICE_TREE_SRC := ${SOURCE_DIR}/linux/linux-tk1-initrd-dtb-secure
else
	DEVICE_TREE_SRC := ${SOURCE_DIR}/linux/linux-tk1-dtb-secure
endif

ifeq (${CONFIG_VM_TK1_INITRD_ROOTFS},y)
	TK1_LINUX_BINARY := ${SOURCE_DIR}/linux/linux-tk1-initrd
else
	TK1_LINUX_BINARY := ${SOURCE_DIR}/linux/linux-tk1-debian
endif

$(STAGE_DIR)/linux/linux-dtb: $(DEVICE_TREE_SRC)
	$(Q)mkdir -p $(dir $@)
	cp $(DEVICE_TREE_SRC) $@

$(STAGE_DIR)/linux/linux: $(TK1_LINUX_BINARY)
	$(Q)mkdir -p $(dir $@)
	cp $(TK1_LINUX_BINARY) $@

COMPONENTS := $(STAGE_DIR)/linux/linux $(STAGE_DIR)/linux/linux-dtb

${BUILD_DIR}/src/Virtual_Machine_inst/static/archive.o: ${COMPONENTS}
	$(Q)mkdir -p $(dir $@)
	${COMMON_PATH}/files_to_obj.sh $@ _cpio_archive $^

$(Virtual_Machine_CFILES:%.c=%.o) $(COMPONENTS): $(srctree)/.config

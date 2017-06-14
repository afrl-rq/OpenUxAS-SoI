# This flag is used by encrypt/decrypt to determine where endian.h is found
# Would be nice to give it a better name
CFLAGS += -DODROID

# Start with the generated Makefile from AADL Trusted Build
include ${PWD}/apps/soi_tk1/make_template/Makefile


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


$(VM_CFILES:%.c=%.o) $(COMPONENTS): $(srctree)/.config

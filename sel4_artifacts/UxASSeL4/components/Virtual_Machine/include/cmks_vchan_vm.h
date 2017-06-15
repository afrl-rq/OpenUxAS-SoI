/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef CMK_VM_VCHAN_COMP_H
#define CMK_VM_VCHAN_COMP_H

#include <autoconf.h>
#include "vmlinux.h"

#include <sel4arm-vmm/vm.h>
#include <sel4arm-vmm/images.h>
#include <sel4arm-vmm/plat/devices.h>
#include <sel4arm-vmm/devices/vgic.h>
#include <sel4arm-vmm/devices/vram.h>
#include <sel4arm-vmm/devices/vusb.h>
#include <sel4utils/irq_server.h>
#include <cpio/cpio.h>

#ifdef CONFIG_VM_VCHAN
void vchan_entry_point(vm_t *vm, uint32_t data);
void vm_vchan_setup(vm_t *vm);
#endif //CONFIG_VM_VCHAN

#endif

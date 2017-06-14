/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#include <autoconf.h>

#ifdef CONFIG_PLAT_TK1

#include "vmlinux.h"

#include <string.h>

#include <vka/capops.h>
#include <camkes.h>

#include <sel4arm-vmm/vm.h>
#include <sel4arm-vmm/images.h>
#include <sel4arm-vmm/plat/devices.h>
#include <sel4arm-vmm/devices/vgic.h>
#include <sel4arm-vmm/devices/vram.h>
#include <sel4utils/irq_server.h>
#include <cpio/cpio.h>

#include <sel4arm-vmm/devices/generic_forward.h>

#define ATAGS_ADDR        (LINUX_RAM_BASE + 0x100)
#define DTB_ADDR          (LINUX_RAM_BASE + 0x01000000)

#define MACH_TYPE_SPECIAL    ~0
#define MACH_TYPE            MACH_TYPE_SPECIAL
#define PAGE_SIZE_BITS 12

extern int start_extra_frame_caps;

extern char _cpio_archive[];

extern vka_t _vka;
extern vspace_t _vspace;
extern irq_server_t _irq_server;
extern seL4_CPtr _fault_endpoint;


#ifdef CONFIG_VM_TK1_EMMC_ROOTFS
int handle_sdmmc4(struct device* d, vm_t* vm, fault_t* fault){
    uint32_t data = fault_get_data(fault);
    uint32_t addr = fault_get_address(fault);
    uint32_t mask = fault_get_data_mask(fault);

    // 0x0600-0x07ff is SDMMC-4, ignore everything else
    uint32_t offset = addr - SDMMC_PADDR;
    if (offset < 0x0600 || offset > 0x07ff) {
        fault_set_data(fault, 0);
        return advance_fault(fault);
    }

    if (fault_is_write(fault)) {
        switch (fault_get_width(fault)) {
            case WIDTH_BYTE:
                *(volatile uint8_t *) addr = (uint8_t) data;
                break;
            case WIDTH_HALFWORD:
                *(volatile uint16_t *) addr = (uint16_t) data;
                break;
            case WIDTH_WORD:
                *(volatile uint32_t *) addr = (uint32_t) data;
                break;
            case WIDTH_DOUBLEWORD:
            default:
                /* Should never get here... Keep the compiler happy */
                assert(0);
        }
    } else {
        addr = addr & ~0x3;
        data = *(volatile uint32_t *) addr;
        fault_set_data(fault, data);
    }
    return advance_fault(fault);
}

const struct device dev_sdmmc4 = {
    .devid = DEV_CUSTOM,
    .name = "SDMMC-4",
    .pstart = SDMMC_PADDR,
    .size = PAGE_SIZE,
    .handle_page_fault = &handle_sdmmc4,
    .priv = NULL
};
#endif //CONFIG_VM_TK1_EMMC_ROOTFS

#ifndef CONFIG_TK1_VM_HACK
const struct device dev_vm_hack_blank = {
    .devid = DEV_CUSTOM,
    .name = "VM Hack - empty space",
    .pstart = 0xd0000000,
    .size = 2*PAGE_SIZE,
    .handle_page_fault = NULL,
    .priv = NULL
};
#endif

static const struct device *linux_pt_devices[] = {
    &dev_usb1,
    &dev_usb3,
};

static const struct device *linux_ram_devices[] = {
    &dev_rtc_kbc_pmc,       // APBDEV_PMC_SCRATCH20_0 "general purpose register storage"
    &dev_data_memory,       // DATA MEMORY "RAM"
    &dev_exception_vectors, // Exception Vectors
    &dev_system_registers,  // System Registers
    &dev_ictlr,             // PRI_ICTRL_CPU_IER_CLR_0 "Clear interrupt enable for CPU0 register"
    &dev_apb_misc,          // APB_MISC_GP_HIDREV_0 "Chip ID Revision Register"
    &dev_fuse,              // FUSE
    &dev_gpios,             // GPIO_INT_ENB_0
#ifndef CONFIG_TK1_VM_HACK
    &dev_vm_hack_blank
#endif
};

static const int linux_pt_irqs[] = {
INTERRUPT_VTIMER               ,
INTERRUPT_USB2                 ,
INTERRUPT_SDMMC4               ,
INTERRUPT_UARTD                ,
INTERRUPT_USB3                 ,
};

static seL4_CPtr linux_pt_irq_caps[ARRAY_SIZE(linux_pt_irqs)];

struct pwr_token {
    const char* linux_bin;
    const char* device_tree;
} pwr_token;

static void* install_linux_kernel(vm_t* vm, const char* kernel_name);
static uint32_t install_linux_dtb(vm_t* vm, const char* dtb_name);

static int
vm_shutdown_cb(vm_t* vm, void* token)
{
    printf("Received shutdown from linux\n");
    return -1;
}

static int
vm_reboot_cb(vm_t* vm, void* token)
{
    struct pwr_token* pwr_token = (struct pwr_token*)token;
    uint32_t dtb_addr;
    void* entry;
    int err;
    printf("Received reboot from linux\n");
    entry = install_linux_kernel(vm, pwr_token->linux_bin);
    dtb_addr = install_linux_dtb(vm, pwr_token->device_tree);
    if (entry == NULL || dtb_addr == 0) {
        printf("Failed to reload linux\n");
        return -1;
    }
    err = vm_set_bootargs(vm, entry, MACH_TYPE, dtb_addr);
    if (err) {
        printf("Failed to set boot args\n");
        return -1;
    }
    err = vm_start(vm);
    if (err) {
        printf("Failed to restart linux\n");
        return -1;
    }
    printf("VM restarted\n");
    return 0;
}

#ifdef CONFIG_TK1_DEVICE_FWD
static struct generic_forward_cfg camkes_uart_d = {
  .read_fn = uartfwd_read,
  .write_fn = uartfwd_write
};

static struct generic_forward_cfg camkes_clk_car =  {
  .read_fn = clkcarfwd_read,
  .write_fn = clkcarfwd_write
};
#endif

#define BBOX_PADDR 0xC0000000

static int
handle_bbox_fault(struct device* d, vm_t* vm, fault_t* fault)
{
    uint32_t offset = fault_get_address(fault) - BBOX_PADDR;

    if (fault_is_write(fault)) {
        uint32_t data = fault_get_data(fault) & 0xFFFF;
        switch (offset) {
        case 0x0:
            bbox->left = data;
            break;
        case 0x2:
            bbox->right = data;
            break;
        case 0x4:
            bbox->top = data;
            break;
        case 0x6:
            bbox->bottom = data;
            bbox_notification_emit();
            break;
        default:
            ZF_LOGE("Unhandled offset");
            break;
        }
    } else {
        fault_set_data(fault, 0);
    }

    return advance_fault(fault);
}

const struct device dev_bbox = {
    .devid = DEV_CUSTOM,
    .name = "Camera bounding box",
    .pstart = BBOX_PADDR,
    .size = PAGE_SIZE,
    .handle_page_fault = &handle_bbox_fault,
    .priv = NULL
};

static int
install_linux_devices(vm_t* vm)
{
    int err;
    int i;
    /* Install virtual devices */
    err = vm_install_vgic(vm);
    assert(!err);
    err = vm_install_ram_range(vm, LINUX_RAM_BASE, LINUX_RAM_SIZE);
    assert(!err);

#ifdef CONFIG_TK1_DEVICE_FWD
    /* Configure UART forward device */
    err = vm_install_generic_forward_device(vm, &dev_vconsole, camkes_uart_d);
    assert(!err);

    /* Configure Clock and Reset forward device */
    err = vm_install_generic_forward_device(vm, &dev_clkcar, camkes_clk_car);
    assert(!err);
#endif // CONFIG_TK1_DEVICE_FWD

    /* Install bounding box "device" to act as barebones vchan */
    err = vm_add_device(vm, &dev_bbox);
    assert(!err);

#ifdef CONFIG_VM_TK1_EMMC_ROOTFS    
    void *addr;
    addr = map_device(vm->vmm_vspace, vm->vka, vm->simple, SDMMC_PADDR, SDMMC_PADDR, seL4_AllRights);
    assert(addr);

    err = vm_add_device(vm, &dev_sdmmc4);
    assert(!err);
#endif // CONFIG_VM_TK1_EMMC_ROOTFS

    err = vm_install_tk1_usb_passthrough_device(vm);
    assert(!err);

    /* Install pass through devices */
    for (i = 0; i < sizeof(linux_pt_devices) / sizeof(*linux_pt_devices); i++) {
       err = vm_install_passthrough_device(vm, linux_pt_devices[i]);
       assert(!err);
    }

    /* Install ram backed devices */
    /* Devices that are just anonymous memory mappings */
    for (i = 0; i < sizeof(linux_ram_devices) / sizeof(*linux_ram_devices); i++) {
        err = vm_install_ram_only_device(vm, linux_ram_devices[i]);
        assert(!err);
    }

    /* hack to give access to other components
       see https://github.com/smaccm/vm_hack/blob/master/details.md for details */
    int offset = 0;
    for (i = 0; i < num_extra_frame_caps; i++) {
        err = vm_map_frame(vm, start_extra_frame_caps + i,
            extra_frame_map_address + offset, PAGE_SIZE_BITS, 1, seL4_AllRights);
        if (err) {
            ZF_LOGF("Failed to map in hacked page %d. "
                    "Did you forget to hand edit the capdl file?", i);
        }
        offset += PAGE_SIZE;
    }

    return 0;
}

static void
do_irq_server_ack(void* token)
{
    struct irq_data* irq_data = (struct irq_data*)token;
    irq_data_ack_irq(irq_data);
}

static void
irq_handler(struct irq_data* irq_data)
{
    virq_handle_t virq;
    int err;
    virq = (virq_handle_t)irq_data->token;
    err = vm_inject_IRQ(virq);
    assert(!err);
}

static int
route_irqs(vm_t* vm, irq_server_t irq_server)
{
    int i;
    for (i = 0; i < ARRAY_SIZE(linux_pt_irqs); i++) {
        irq_t irq = linux_pt_irqs[i];
        struct irq_data* irq_data;
        virq_handle_t virq;
        void (*handler)(struct irq_data*);
        handler = &irq_handler;
        irq_data = irq_server_register_irq(irq_server, irq, handler, NULL);
        if (!irq_data) {
            return -1;
        }
        linux_pt_irq_caps[i] = irq_data->cap;
        virq = vm_virq_new(vm, irq, &do_irq_server_ack, irq_data);
        if (virq == NULL) {
            return -1;
        }
        irq_data->token = (void*)virq;
    }
    return 0;
}

void delete_irqs(seL4_CPtr root) {
    for (int i = 0; i < ARRAY_SIZE(linux_pt_irq_caps); i++) {
        seL4_CPtr cap = linux_pt_irq_caps[i];
        if (cap != 0) {
            int err = seL4_CNode_Delete(root, cap, 32);
            assert(!err);
            linux_pt_irq_caps[i] = 0;
        }
    }
}

static uint32_t
install_linux_dtb(vm_t* vm, const char* dtb_name)
{
    void* file;
    unsigned long size;
    uint32_t dtb_addr;

    /* Retrieve the file data */
    file = cpio_get_file(_cpio_archive, dtb_name, &size);
    if (file == NULL) {
        printf("Error: Linux dtb file \'%s\' not found\n", dtb_name);
        return 0;
    }
    if (image_get_type(file) != IMG_DTB) {
        printf("Error: \'%s\' is not a device tree\n", dtb_name);
        return 0;
    }

    /* Copy the tree to the VM */
    dtb_addr = DTB_ADDR;
    if (vm_copyout(vm, file, dtb_addr, size)) {
        printf("Error: Failed to load device tree \'%s\'\n", dtb_name);
        return 0;
    } else {
        return dtb_addr;
    }

}

static void*
install_linux_kernel(vm_t* vm, const char* kernel_name)
{
    void* file;
    unsigned long size;
    uintptr_t entry;

    /* Retrieve the file data */
    file = cpio_get_file(_cpio_archive, kernel_name, &size);
    if (file == NULL) {
        printf("Error: Unable to find kernel image \'%s\'\n", kernel_name);
        return NULL;
    }

    /* Determine the load address */
    switch (image_get_type(file)) {
    case IMG_BIN:
        entry = LINUX_RAM_BASE + 0x8000;
        break;
    case IMG_ZIMAGE:
        entry = zImage_get_load_address(file, LINUX_RAM_BASE);
        break;
    default:
        printf("Error: Unknown Linux image format for \'%s\'\n", kernel_name);
        return NULL;
    }
    /* Load the image */
    if (vm_copyout(vm, file, entry, size)) {
        printf("Error: Failed to load \'%s\'\n", kernel_name);
        return NULL;
    } else {
        return (void*)entry;
    }
}

int
load_linux(vm_t* vm, const char* kernel_name, const char* dtb_name)
{
    void* entry;
    uint32_t dtb;
    int err;

    pwr_token.linux_bin = kernel_name;
    pwr_token.device_tree = dtb_name;

    /* Install devices */
    err = install_linux_devices(vm);
    if (err) {
        printf("Error: Failed to install Linux devices\n");
        return -1;
    }
    /* Route IRQs */
    err = route_irqs(vm, _irq_server);
    if (err) {
        return -1;
    }
    /* Load kernel */
    entry = install_linux_kernel(vm, kernel_name);
    if (!entry) {
        return -1;
    }
    /* Load device tree */
    dtb = install_linux_dtb(vm, dtb_name);
    if (!dtb) {
        return -1;
    }

    /* Set boot arguments */
    err = vm_set_bootargs(vm, entry, MACH_TYPE, dtb);
    if (err) {
        printf("Error: Failed to set boot arguments\n");
        return -1;
    }

    return 0;
}
#endif

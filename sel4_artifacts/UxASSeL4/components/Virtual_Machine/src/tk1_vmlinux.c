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
#include <sel4arm-vmm/devices/vusb.h>
#include <sel4utils/irq_server.h>
#include <cpio/cpio.h>
#include <tb_soi_tk1_types.h>

#include <sel4arm-vmm/devices/generic_forward.h>

#define ATAGS_ADDR        (LINUX_RAM_BASE + 0x100)
#define DTB_ADDR          (LINUX_RAM_BASE + 0x01000000)

#define MACH_TYPE_SPECIAL    ~0
#define MACH_TYPE            MACH_TYPE_SPECIAL
#define PAGE_SIZE_BITS 12

//extern int start_extra_frame_caps;

extern char _cpio_archive[];

extern vka_t _vka;
extern vspace_t _vspace;
extern irq_server_t _irq_server;
extern seL4_CPtr _fault_endpoint;

//BEGIN SOI SPECIFIC STUFF

bool wm_read = false;
void handle_mission_read(uint32_t * var){
    //printf("VM saw mission read from WM\n");
    uint32_t numBytes;
    tb_mission_read_dequeue(&numBytes);
    wm_read_post();
    tb_mission_read_notification_reg_callback(handle_mission_read, NULL);
}

pre_init(void){
    tb_mission_read_notification_reg_callback(handle_mission_read, NULL);
}


bool mission_write
(const bool * tb_mission_write) {
    bool tb_result = true ; 

    tb_result &= tb_mission_write0_enqueue((bool *)tb_mission_write);

    return tb_result;
}

static int handle_waypoint_fault(struct device* d, vm_t* vm, fault_t* fault){
//    vusb_device_t* vusb;
//    usb_ctrl_regs_t *ctrl_regs;
//    uint32_t* reg;
//    int offset;
//
//    assert(d->priv);
//    offset = fault_get_address(fault) - d->pstart - 0x1000;
//    vusb = device_to_vusb_dev_data(d);
//    ctrl_regs = vusb->ctrl_regs;
//    reg = (uint32_t*)((void*)ctrl_regs + (offset & ~0x3));
//    if (fault_is_read(fault)) {
//        if (reg != &ctrl_regs->status) {
//            fault_set_data(fault, *reg);
//        }
//    } else {
//        if (reg == &ctrl_regs->status) {
//            /* start a transfer */
//            root_hub_ctrl_start(vusb->hcd, ctrl_regs);
//        } else if (reg == &ctrl_regs->intr) {
//            /* Clear the interrupt pending flag */
//            *reg = fault_emulate(fault, *reg);
//        } else if (reg == &ctrl_regs->notify) {
//            /* Manual notification */
//            vm_vusb_notify(vusb);
//        } else if (reg == &ctrl_regs->cancel_transaction) {
//            /* Manual notification */
//            vm_vusb_cancel(vusb, fault_get_data(fault));
//        } else if ((void*)reg >= (void*)&ctrl_regs->req) {
//            /* Fill out the root hub USB request */
//            *reg = fault_emulate(fault, *reg);
//        }
//    }   
//    return advance_fault(fault);
    int addr;
    uint8_t data;
    static uint32_t bufIndex;
    //MissionSoftware__mission_command_impl buf;

    addr = fault_get_address(fault);
    //printf("VM RECEIVED FAULT at addr:%x\n", addr);

    if(addr == 0xe0000001){
        //this indicates the begining of a write
        bufIndex = 0;
    }else if(addr == 0xe0000002){
        //this indicates the end of a write
        mission_write(&bufIndex);
        //this is kind of bad because the VM will halt
        //execution until everything is has been sent to the AP
        wm_read_wait();
    }else if(addr == 0xe0000000){
        //this indicates data being written
        if(fault_is_write(fault)){
            data = (uint8_t)fault_get_data(fault);
            (*mission)[bufIndex++] = data;
        }
    }else{
        assert(0);
    }

    return ignore_fault(fault);
}

const struct device dev_uxas_waypoint = {
    .devid = DEV_CUSTOM,
    .name = "waypoint",
    .pstart = 0xE0000000, //this is an empty address on the tk1
    .size = 0x1000,
    .handle_page_fault = handle_waypoint_fault,
    .priv = NULL
};

//END SOI SPECIFC STUFF

static const struct device *linux_pt_devices[] = {
    &dev_usb1,
    &dev_usb3,
    &dev_sdmmc,
};

static const struct device *linux_ram_devices[] = {
#ifndef CONFIG_TK1_INSECURE
    &dev_rtc_kbc_pmc,
    &dev_data_memory,
    &dev_exception_vectors,
    &dev_system_registers,
    &dev_ictlr,
    &dev_apb_misc,
    &dev_fuse,
    &dev_gpios,
#endif /* CONFIG_TK1_INSECURE */
};

static const int linux_pt_irqs[] = {
INTERRUPT_VTIMER               ,
INTERRUPT_USB2                 ,
INTERRUPT_SDMMC4               ,
INTERRUPT_UARTD                ,
INTERRUPT_USB3,
#ifdef CONFIG_TK1_INSECURE
INTERRUPT_TMR1                 ,
INTERRUPT_TMR2                 ,
INTERRUPT_RTC                  ,
INTERRUPT_CEC                  ,
INTERRUPT_SHR_SEM_INBOX_FULL   ,
INTERRUPT_SHR_SEM_INBOX_EMPTY  ,
INTERRUPT_SHR_SEM_OUTBOX_FULL  ,
INTERRUPT_SHR_SEM_OUTBOX_EMPTY ,
INTERRUPT_VDE_UCQ              ,
INTERRUPT_VDE_SYNC_TOKEN       ,
INTERRUPT_VDE_BSEV             ,
INTERRUPT_VDE_BSEA             ,
INTERRUPT_VDE_SXE              ,
INTERRUPT_SATA_RX_STAT         ,
INTERRUPT_SDMMC1               ,
INTERRUPT_SDMMC2               ,
INTERRUPT_VDE                  ,
INTERRUPT_AVP_UCQ              ,
INTERRUPT_SDMMC3               ,
INTERRUPT_USB                  ,
INTERRUPT_SATA_CTL             ,
INTERRUPT_VCP                  ,
INTERRUPT_APB_DMA_CPU          ,
INTERRUPT_AHB_DMA_CPU          ,
INTERRUPT_ARB_SEM_GNT_COP      ,
INTERRUPT_ARB_SEM_GNT_CPU      ,
INTERRUPT_OWR                  ,
INTERRUPT_GPIO1                ,
INTERRUPT_GPIO2                ,
INTERRUPT_GPIO3                ,
INTERRUPT_GPIO4                ,
INTERRUPT_UARTA                ,
INTERRUPT_UARTB                ,
INTERRUPT_I2C                  ,
INTERRUPT_USB3_HOST            ,
INTERRUPT_USB3_HOST_SMI        ,
INTERRUPT_TMR3                 ,
INTERRUPT_TMR4                 ,
INTERRUPT_USB3_HOST_PME        ,
INTERRUPT_USB3_DEV_HOST        ,
INTERRUPT_ACTMON               ,
INTERRUPT_UARTC                ,
INTERRUPT_HSI                  ,
INTERRUPT_THERMAL              ,
INTERRUPT_XUSB_PADCTL          ,
INTERRUPT_TSEC                 ,
INTERRUPT_EDP                  ,
INTERRUPT_VFIR                 ,
INTERRUPT_I2C5                 ,
INTERRUPT_STAT_MON             ,
INTERRUPT_GPIO5                ,
INTERRUPT_USB3_DEV_SMI         ,
INTERRUPT_USB3_DEV_PME         ,
INTERRUPT_SE                   ,
INTERRUPT_SPI1                 ,
INTERRUPT_APB_DMA_COP          ,
INTERRUPT_AHB_DMA_COP          ,
INTERRUPT_CLDVFS               ,
INTERRUPT_I2C6                 ,
INTERRUPT_HOST1X_SYNCPT_COP    ,
INTERRUPT_HOST1X_SYNCPT_CPU    ,
INTERRUPT_HOST1X_GEN_COP       ,
INTERRUPT_HOST1X_GEN_CPU       ,
INTERRUPT_MSENC                ,
INTERRUPT_VI                   ,
INTERRUPT_ISPB                 ,
INTERRUPT_ISP                  ,
INTERRUPT_VIC                  ,
INTERRUPT_DISPLAY              ,
INTERRUPT_DISPLAYB             ,
INTERRUPT_HDMI                 ,
INTERRUPT_SOR                  ,
INTERRUPT_EMC                  ,
INTERRUPT_SPI6                 ,
INTERRUPT_HDA                  ,
INTERRUPT_SPI2                 ,
INTERRUPT_SPI3                 ,
INTERRUPT_I2C2                 ,
INTERRUPT_PMU_EXT              ,
INTERRUPT_GPIO6                ,
INTERRUPT_GPIO7                ,
INTERRUPT_I2C3                 ,
INTERRUPT_SW                   ,
INTERRUPT_SNOR                 ,
INTERRUPT_PCIE_INT             ,
INTERRUPT_PCIE_MSI             ,
INTERRUPT_PCIE_WAKE            ,
INTERRUPT_AVP_CACHE            ,
INTERRUPT_AUDIO_CLUSTER        ,
INTERRUPT_APB_DMA_CH0          ,
INTERRUPT_APB_DMA_CH1          ,
INTERRUPT_APB_DMA_CH2          ,
INTERRUPT_APB_DMA_CH3          ,
INTERRUPT_APB_DMA_CH4          ,
INTERRUPT_APB_DMA_CH5          ,
INTERRUPT_APB_DMA_CH6          ,
INTERRUPT_APB_DMA_CH7          ,
INTERRUPT_APB_DMA_CH8          ,
INTERRUPT_APB_DMA_CH9          ,
INTERRUPT_APB_DMA_CH10         ,
INTERRUPT_APB_DMA_CH11         ,
INTERRUPT_APB_DMA_CH12         ,
INTERRUPT_APB_DMA_CH13         ,
INTERRUPT_APB_DMA_CH14         ,
INTERRUPT_APB_DMA_CH15         ,
INTERRUPT_I2C4                 ,
INTERRUPT_TMR5                 ,
INTERRUPT_HIER_GROUP1_COP      ,
INTERRUPT_WDT_CPU              ,
INTERRUPT_WDT_AVP              ,
INTERRUPT_GPIO8                ,
INTERRUPT_CAR                  ,
INTERRUPT_HIER_GROUP1_CPU      ,
INTERRUPT_APB_DMA_CH16         ,
INTERRUPT_APB_DMA_CH17         ,
INTERRUPT_APB_DMA_CH18         ,
INTERRUPT_APB_DMA_CH19         ,
INTERRUPT_APB_DMA_CH20         ,
INTERRUPT_APB_DMA_CH21         ,
INTERRUPT_APB_DMA_CH22         ,
INTERRUPT_APB_DMA_CH23         ,
INTERRUPT_APB_DMA_CH24         ,
INTERRUPT_APB_DMA_CH25         ,
INTERRUPT_APB_DMA_CH26         ,
INTERRUPT_APB_DMA_CH27         ,
INTERRUPT_APB_DMA_CH28         ,
INTERRUPT_APB_DMA_CH29         ,
INTERRUPT_APB_DMA_CH30         ,
INTERRUPT_APB_DMA_CH31         ,
INTERRUPT_CPU0_PMU             ,
INTERRUPT_CPU1_PMU             ,
INTERRUPT_CPU2_PMU             ,
INTERRUPT_CPU3_PMU             ,
INTERRUPT_SDMMC1_SYS           ,
INTERRUPT_SDMMC2_SYS           ,
INTERRUPT_SDMMC3_SYS           ,
INTERRUPT_SDMMC4_SYS           ,
INTERRUPT_TMR6                 ,
INTERRUPT_TMR7                 ,
INTERRUPT_TMR8                 ,
INTERRUPT_TMR9                 ,
INTERRUPT_TMR0                 ,
INTERRUPT_GPU                  ,
INTERRUPT_GPU_NONSTALL         ,
ARDPAUX                        ,
#endif
};

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

#if defined FEATURE_VUSB

static vusb_device_t* _vusb;
static usb_host_t _hcd;

static void
usb_irq_handler(struct irq_data* irq_data)
{
    usb_host_t* hcd = (usb_host_t*)irq_data->token;
    usb_hcd_handle_irq(hcd);
    irq_data_ack_irq(irq_data);
}

static int
install_vusb(vm_t* vm)
{
    irq_server_t irq_server;
    ps_io_ops_t* io_ops;
    vusb_device_t* vusb;
    usb_host_t* hcd;
    struct irq_data* irq_data;
    seL4_CPtr vmm_ep;
    int err;
    irq_server = _irq_server;
    io_ops = vm->io_ops;
    hcd = &_hcd;
    vmm_ep = _fault_endpoint;

    /* Initialise the physical host controller */
    err = usb_host_init(USB_HOST_DEFAULT, io_ops, hcd);
    assert(!err);
    if (err) {
        return -1;
    }

    /* Route physical IRQs */
    irq_data = irq_server_register_irq(irq_server, 103, usb_irq_handler, hcd);
    if (!irq_data) {
        return -1;
    }
    /* Install the virtual device */
    vusb = vm_install_vusb(vm, hcd, VUSB_ADDRESS, VUSB_IRQ, vmm_ep, VUSB_NINDEX,
                           VUSB_NBADGE);
    assert(vusb != NULL);
    if (vusb == NULL) {
        return -1;
    }
    _vusb = vusb;

    return 0;
}

void
vusb_notify(void)
{
    vm_vusb_notify(_vusb);
}

#else /* FEATURE_VUSB */

#include <platsupport/gpio.h>

#define NRESET_GPIO              XEINT12
#define HUBCONNECT_GPIO          XEINT6
#define NINT_GPIO                XEINT7

static int
install_vusb(vm_t* vm)
{
    /* TODO for TK1 */
    return 0;
}

void
vusb_notify(void)
{
}

#endif /* FEATURE_VUSB */

static void
configure_gpio(vm_t *vm)
{
#ifdef CONFIG_APP_LINUX_SECURE
    /* Don't provide any access to GPIO/MUX */
#else /* CONFIG_APP_LINUX_SECURE */
    /* TODO for TK1 */
#endif /* CONFIG_APP_LINUX_SECURE */
}

#ifdef CONFIG_TK1_DEVICE_FWD
struct generic_forward_cfg camkes_uart_d = {
  .read_fn = uartfwd_read,
  .write_fn = uartfwd_write
};

struct generic_forward_cfg camkes_clk_car =  {
  .read_fn = clkcarfwd_read,
  .write_fn = clkcarfwd_write
};

#endif
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

    /* Install virtual USB */
    err = install_vusb(vm);
    assert(!err);

#if CONFIG_APP_LINUX_SECURE
    /* Add hooks for specific power management hooks */
    err = vm_install_vpower(vm, &vm_shutdown_cb, &pwr_token, &vm_reboot_cb, &pwr_token);
    assert(!err);
#else
#endif /* CONFIG_APP_LINUX_SECURE */

    configure_gpio(vm);
#ifdef CONFIG_TK1_DEVICE_FWD
    /* Configure UART forward device */
    err = vm_install_generic_forward_device(vm, &dev_vconsole, camkes_uart_d);
    assert(!err);

    /* Configure Clock and Reset forward device */
    err = vm_install_generic_forward_device(vm, &dev_clkcar, camkes_clk_car);
    assert(!err);
#endif // CONFIG_TK1_DEVICE_FWD

    err = vm_install_tk1_usb_passthrough_device(vm);
    assert(!err);

    /* Install pass through devices */
    /* In insecure mode TK1 passes through all devices at the moment by using on-demand device mapping */
    for (i = 0; i < sizeof(linux_pt_devices) / sizeof(*linux_pt_devices); i++) {
        err = vm_install_passthrough_device(vm, linux_pt_devices[i]);
        assert(!err);
    }

    err = vm_add_device(vm, &dev_uxas_waypoint);

    /* Install ram backed devices */
    /* Devices that are just anonymous memory mappings */
    for (i = 0; i < sizeof(linux_ram_devices) / sizeof(*linux_ram_devices); i++) {
        err = vm_install_ram_only_device(vm, linux_ram_devices[i]);
        assert(!err);
    }

    ///* hack to give access to other components
    //   see https://github.com/smaccm/vm_hack/blob/master/details.md for details */
    //int offset = 0;
    //for (i = 0; i < num_extra_frame_caps; i++) {
    //    err = vm_map_frame(vm, start_extra_frame_caps + i,
    //        extra_frame_map_address + offset, PAGE_SIZE_BITS, 1, seL4_AllRights);
    //    assert(!err);
    //    offset += PAGE_SIZE;
    //}

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
        virq = vm_virq_new(vm, irq, &do_irq_server_ack, irq_data);
        if (virq == NULL) {
            return -1;
        }
        irq_data->token = (void*)virq;
    }
    return 0;
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

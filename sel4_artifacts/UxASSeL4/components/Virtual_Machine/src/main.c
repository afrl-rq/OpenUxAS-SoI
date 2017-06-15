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

#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <setjmp.h>

#include <allocman/allocman.h>
#include <allocman/bootstrap.h>
#include <allocman/vka.h>
#include <vka/capops.h>
#include <vka/object.h>

#include <vspace/vspace.h>
#include <simple/simple.h>
#include <simple/simple_helpers.h>
#include <simple-default/simple-default.h>
#include <platsupport/io.h>
#include <sel4platsupport/platsupport.h>
#include <sel4platsupport/io.h>

#include <cpio/cpio.h>

#include <sel4arm-vmm/vm.h>
#include <sel4arm-vmm/guest_vspace.h>
#include <sel4utils/irq_server.h>
#include <dma/dma.h>

#include <camkes.h>
#include <camkes/tls.h>

#include "vmlinux.h"
#include "cmks_vchan_vm.h"

int start_extra_frame_caps;

int VM_PRIO = 100;
#define VM_BADGE            (1U << 0)
#define VM_LINUX_NAME       "linux"
#define VM_LINUX_DTB_NAME   "linux-dtb"
#define VM_NAME             "Linux"

#define IRQSERVER_PRIO      (VM_PRIO + 1)
#define IRQ_MESSAGE_LABEL   0xCAFE

#define DMA_VSTART  0x40000000

#ifndef DEBUG_BUILD
#define seL4_DebugHalt() do{ printf("Halting...\n"); while(1); } while(0)
#endif

vka_t _vka;
simple_t _simple;
vspace_t _vspace;
sel4utils_alloc_data_t _alloc_data;
allocman_t *allocman;
static char allocator_mempool[83886080];
seL4_CPtr _fault_endpoint;
irq_server_t _irq_server;

struct ps_io_ops _io_ops;

extern char _cpio_archive[];

static jmp_buf restart_jmp_buf;

static void
print_cpio_info(void)
{
    struct cpio_info info;
    const char* name;
    unsigned long size;
    int i;

    cpio_info(_cpio_archive, &info);

    printf("CPIO: %d files found.\n", info.file_count);
    assert(info.file_count > 0);
    for (i = 0; i < info.file_count; i++) {
        void * addr;
        char buf[info.max_path_sz + 1];
        buf[info.max_path_sz] = '\0';
        addr = cpio_get_entry(_cpio_archive, i, &name, &size);
        assert(addr);
        strncpy(buf, name, info.max_path_sz);
        printf("%d) %-20s  0x%08x, %8ld bytes\n", i, buf, (uint32_t)addr, size);
    }
    printf("\n");
}

void camkes_make_simple(simple_t *simple);

static int
_dma_morecore(size_t min_size, int cached, struct dma_mem_descriptor* dma_desc)
{
    static uint32_t _vaddr = DMA_VSTART;
    struct seL4_ARM_Page_GetAddress getaddr_ret;
    seL4_CPtr frame;
    seL4_CPtr pd;
    vka_t* vka;
    int err;

    pd = simple_get_pd(&_simple);
    vka = &_vka;

    /* Create a frame */
    frame = vka_alloc_frame_leaky(vka, 12);
    assert(frame);
    if (!frame) {
        return -1;
    }

    /* Try to map the page */
    err = seL4_ARM_Page_Map(frame, pd, _vaddr, seL4_AllRights, 0);
    if (err) {
        seL4_CPtr pt;
        /* Allocate a page table */
        pt = vka_alloc_page_table_leaky(vka);
        if (!pt) {
            printf("Failed to create page table\n");
            return -1;
        }
        /* Map the page table */
        err = seL4_ARM_PageTable_Map(pt, pd, _vaddr, 0);
        if (err) {
            printf("Failed to map page table\n");
            return -1;
        }
        /* Try to map the page again */
        err = seL4_ARM_Page_Map(frame, pd, _vaddr, seL4_AllRights, 0);
        if (err) {
            printf("Failed to map page\n");
            return -1;
        }

    }

    /* Find the physical address of the page */
    getaddr_ret = seL4_ARM_Page_GetAddress(frame);
    assert(!getaddr_ret.error);
    /* Setup dma memory description */
    dma_desc->vaddr = _vaddr;
    dma_desc->paddr = getaddr_ret.paddr;
    dma_desc->cached = 0;
    dma_desc->size_bits = 12;
    dma_desc->alloc_cookie = (void*)frame;
    dma_desc->cookie = NULL;
    /* Advance the virtual address marker */
    _vaddr += BIT(12);
    return 0;
}

typedef struct vm_io_cookie {
    simple_t simple;
    vka_t vka;
    vspace_t vspace;
} vm_io_cookie_t;

static void *
vm_map_paddr_with_page_size(vm_io_cookie_t *io_mapper, uintptr_t paddr, size_t size, int page_size_bits, int cached)
{

    vka_t *vka = &io_mapper->vka;
    vspace_t *vspace = &io_mapper->vspace;
    simple_t *simple = &io_mapper->simple;

    /* search at start of page */
    int page_size = BIT(page_size_bits);
    uintptr_t start = ROUND_DOWN(paddr, page_size);
    uintptr_t offset = paddr - start;
    size += offset;

    /* calculate number of pages */
    unsigned int num_pages = ROUND_UP(size, page_size) >> page_size_bits;
    assert(num_pages << page_size_bits >= size);
    seL4_CPtr frames[num_pages];
    seL4_Word cookies[num_pages];

    /* get all of the physical frame caps */
    for (unsigned int i = 0; i < num_pages; i++) {
        /* allocate a cslot */
        int error = vka_cspace_alloc(vka, &frames[i]);
        if (error) {
            ZF_LOGE("cspace alloc failed");
            assert(error == 0);
            /* we don't clean up as everything has gone to hell */
            return NULL;
        }

        /* create a path */
        cspacepath_t path;
        vka_cspace_make_path(vka, frames[i], &path);

        error = vka_utspace_alloc_at(vka, &path, kobject_get_type(KOBJECT_FRAME, page_size_bits), page_size_bits, start + (i * page_size), &cookies[i]);

        if (error) {
            cookies[i] = -1;
            error = simple_get_frame_cap(simple, (void*)start + (i * page_size), page_size_bits, &path);
            if (error) {
                /* free this slot, and then do general cleanup of the rest of the slots.
                 * this avoids a needless seL4_CNode_Delete of this slot, as there is no
                 * cap in it */
                vka_cspace_free(vka, frames[i]);
                num_pages = i;
                goto error;
            }
        }

    }

    /* Now map the frames in */
    void *vaddr = vspace_map_pages(vspace, frames, NULL, seL4_AllRights, num_pages, page_size_bits, cached);
    if (vaddr) {
        return vaddr + offset;
    }
error:
    for (unsigned int i = 0; i < num_pages; i++) {
        cspacepath_t path;
        vka_cspace_make_path(vka, frames[i], &path);
        vka_cnode_delete(&path);
        if (cookies[i] != -1) {
            vka_utspace_free(vka, kobject_get_type(KOBJECT_FRAME, page_size_bits), page_size_bits, cookies[i]);
        }
        vka_cspace_free(vka, frames[i]);
    }
    return NULL;
}

static void *
vm_map_paddr(void *cookie, uintptr_t paddr, size_t size, int cached, ps_mem_flags_t flags)
{
    vm_io_cookie_t* io_mapper = (vm_io_cookie_t*)cookie;

    int frame_size_index = 0;
    /* find the largest reasonable frame size */
    while (frame_size_index + 1 < SEL4_NUM_PAGE_SIZES) {
        if (size >> sel4_page_sizes[frame_size_index + 1] == 0) {
            break;
        }
        frame_size_index++;
    }

    /* try mapping in this and all smaller frame sizes until something works */
    for (int i = frame_size_index; i >= 0; i--) {
        void *result = vm_map_paddr_with_page_size(io_mapper, paddr, size, sel4_page_sizes[i], cached);
        if (result) {
            return result;
        }
    }
    ZF_LOGE("Failed to map address %p", (void *)paddr);
    return NULL;
}

static void
vm_unmap_vaddr(void *cookie, void *vaddr, size_t size)
{
    ZF_LOGF("Not unmapping vaddr %p", vaddr);
}

static int
vm_new_io_mapper(simple_t simple, vspace_t vspace, vka_t vka, ps_io_mapper_t *io_mapper)
{
    vm_io_cookie_t *cookie;
    cookie = (vm_io_cookie_t*)malloc(sizeof(*cookie));
    if (!cookie) {
        ZF_LOGE("Failed to allocate %zu bytes", sizeof(*cookie));
        return -1;
    }
    *cookie = (vm_io_cookie_t) {
        .vspace = vspace,
        .simple = simple,
        .vka = vka
    };
    *io_mapper = (ps_io_mapper_t) {
        .cookie = cookie,
        .io_map_fn = vm_map_paddr,
        .io_unmap_fn = vm_unmap_vaddr
    };
    return 0;
}

static int
vmm_init(void)
{
    vka_object_t fault_ep_obj;
    vka_t* vka;
    simple_t* simple;
    vspace_t* vspace;
    int err;

    vka = &_vka;
    vspace = &_vspace;
    simple = &_simple;
    fault_ep_obj.cptr = 0;

    /* Camkes adds nothing to our address space, so this array is empty */
    void *existing_frames[] = {
        NULL
    };

    camkes_make_simple(simple);

    start_extra_frame_caps = simple_last_valid_cap(simple) + 1;

    /* Initialize allocator */
    allocman = bootstrap_use_current_1level(
            simple_get_cnode(simple),
            simple_get_cnode_size_bits(simple),
            simple_last_valid_cap(simple) + 1 ,// BACKES + num_extra_frame_caps,
            BIT(simple_get_cnode_size_bits(simple)),
            sizeof(allocator_mempool), allocator_mempool
    );
    assert(allocman);

    allocman_make_vka(vka, allocman);

    for (int i = 0; i < simple_get_untyped_count(simple); i++) {
        size_t size;
        uintptr_t paddr;
        bool device;
        seL4_CPtr cap = simple_get_nth_untyped(simple, i, &size, &paddr, &device);
        cspacepath_t path;
        vka_cspace_make_path(vka, cap, &path);
        int utType = device ? ALLOCMAN_UT_DEV : ALLOCMAN_UT_KERNEL;
        if (utType == ALLOCMAN_UT_DEV &&
            paddr >= LINUX_RAM_PADDR_BASE && paddr <= (LINUX_RAM_PADDR_BASE + (LINUX_RAM_SIZE-1))) {
            utType = ALLOCMAN_UT_DEV_MEM;
        }
        err = allocman_utspace_add_uts(allocman, 1, &path, &size, &paddr, utType);
        assert(!err);
    }

    /* Initialize the vspace */
    err = sel4utils_bootstrap_vspace(vspace, &_alloc_data,
            simple_get_init_cap(simple, seL4_CapInitThreadPD), vka, NULL, NULL, existing_frames);
    assert(!err);

    /* Initialise device support */
    err = vm_new_io_mapper(*simple, *vspace, *vka,
                           &_io_ops.io_mapper);
    assert(!err);

    /* Initialise MUX subsystem for platforms that need it */
#ifndef CONFIG_PLAT_TK1
    err = mux_sys_init(&_io_ops, &_io_ops.mux_sys);
    assert(!err);
#endif

    /* Initialise DMA */
    err = dma_dmaman_init(&_dma_morecore, NULL, &_io_ops.dma_manager);
    assert(!err);

    /* Allocate an endpoint for listening to events */
    err = vka_alloc_endpoint(vka, &fault_ep_obj);
    assert(!err);
    _fault_endpoint = fault_ep_obj.cptr;

    /* Create an IRQ server */
    err = irq_server_new(vspace, vka, simple_get_cnode(simple), IRQSERVER_PRIO,
                         simple, fault_ep_obj.cptr,
                         IRQ_MESSAGE_LABEL, 256, &_irq_server);
    assert(!err);


    return 0;
}

static void
map_unity_ram(vm_t* vm)
{
    /* Dimensions of physical memory that we'll use. Note that we do not map the entirety of RAM.
     */
    static const uintptr_t paddr_start = LINUX_RAM_PADDR_BASE;
    static const uintptr_t paddr_end = paddr_start + LINUX_RAM_SIZE;

    int err;

    uintptr_t start;
    reservation_t res;
    unsigned int bits = seL4_PageBits;
    res = vspace_reserve_range_at(&vm->vm_vspace, (void*)(paddr_start - LINUX_RAM_OFFSET), paddr_end - paddr_start, seL4_AllRights, 1);
    assert(res.res);
    for (start = paddr_start; start < paddr_end; start += BIT(bits)) {
        cspacepath_t frame;
        err = vka_cspace_alloc_path(vm->vka, &frame);
        assert(!err);
        seL4_Word cookie;
        err = vka_utspace_alloc_at(vm->vka, &frame, kobject_get_type(KOBJECT_FRAME, bits), bits, start, &cookie);
        if (err) {
            printf("Failed to map ram page 0x%x\n", start);
            vka_cspace_free(vm->vka, frame.capPtr);
            break;
        }
        uintptr_t addr = start - LINUX_RAM_OFFSET;
        err = vspace_map_pages_at_vaddr(&vm->vm_vspace, &frame.capPtr, &bits, (void*)addr, 1, bits, res);
        assert(!err);
    }
}


void restart_component(void) {
    longjmp(restart_jmp_buf, 1);
}

extern char __bss_start[];
extern char _bss_end__[];
extern char __sysinfo[];
extern char __libc[];
extern char morecore_area[];
extern char morecore_size[];
extern uintptr_t morecore_top;

void reset_resources(void) {
    simple_t simple;
    camkes_make_simple(&simple);
    int i;
    seL4_CPtr root = simple_get_cnode(&simple);
    int error;
    /* revoke any of our initial untyped resources */
    for (i = 0; i < simple_get_untyped_count(&simple); i++) {
        size_t size_bits;
        uintptr_t paddr;
        bool device;
        seL4_CPtr ut = simple_get_nth_untyped(&simple, i, &size_bits, &paddr, &device);
        error = seL4_CNode_Revoke(root, ut, 32);
        assert(error == seL4_NoError);
    }
    /* delete anything from any slots that should be empty */
    for (i = simple_last_valid_cap(&simple) + 1; i < BIT(simple_get_cnode_size_bits(&simple)); i++) {
        seL4_CNode_Delete(root, i, 32);
    }
    /* save some pieces of the bss that we actually don't want to zero */
    char save_sysinfo[4];
    char save_libc[34];
    char save_morecore_area[4];
    char save_morecore_size[4];
    memcpy(save_libc, __libc, 34);
    memcpy(save_sysinfo, __sysinfo, 4);
    memcpy(save_morecore_area, morecore_area, 4);
    memcpy(save_morecore_size, morecore_size, 4);
    /* zero the bss */
    memset(__bss_start, 0, (uintptr_t)_bss_end__ - (uintptr_t)__bss_start);
    /* restore these pieces */
    memcpy(__libc, save_libc, 34);
    memcpy(__sysinfo, save_sysinfo, 4);
    memcpy(morecore_area, save_morecore_area, 4);
    memcpy(morecore_size, save_morecore_size, 4);
    morecore_top = (uintptr_t) &morecore_area[CONFIG_LIB_SEL4_MUSLC_SYS_MORECORE_BYTES];
}

static seL4_CPtr restart_tcb;

//static void restart_event(void *arg) {
//    restart_event_reg_callback(restart_event, NULL);
//    seL4_UserContext context = {
//        .pc = (seL4_Word)restart_component,
//    };
//    seL4_TCB_WriteRegisters(restart_tcb, true, 0, 1, &context);
//}

int
main_continued(void)
{
    vm_t vm;
    int err;

    /* setup for restart with a setjmp */
    while (setjmp(restart_jmp_buf) != 0) {
        err = vm_process_reboot_callbacks(&vm);
        if (err) {
            ZF_LOGF("vm_process_reboot_callbacks failed: %d", err);
        }
        reset_resources();
    }
    restart_tcb = camkes_get_tls()->tcb_cap;
    //restart_event_reg_callback(restart_event, NULL);

    err = vmm_init();
    assert(!err);

    print_cpio_info();

    /* Create the VM */
    err = vm_create(VM_NAME, VM_PRIO, _fault_endpoint, VM_BADGE,
                    &_vka, &_simple, &_vspace, &_io_ops, &vm);
    if (err) {
        printf("Failed to create VM\n");
        seL4_DebugHalt();
        return -1;
    }

#ifdef CONFIG_ARM_SMMU
    /* install any iospaces */
    int iospace_caps;
    err = simple_get_iospace_cap_count(&_simple, &iospace_caps);
    if (err) {
        ZF_LOGF("Failed to get iospace count");
    }
    for (int i = 0; i < iospace_caps; i++) {
        seL4_CPtr iospace = simple_get_nth_iospace_cap(&_simple, i);
        err = vmm_guest_vspace_add_iospace(&_vspace, &vm.vm_vspace, iospace);
        if (err) {
            ZF_LOGF("Failed to add iospace");
        }
    }
#endif /* CONFIG_ARM_SMMU */

#ifdef CONFIG_PLAT_EXYNOS5410
    /* HACK: See if we have a "RAM device" for 1-1 mappings */
    map_unity_ram(&vm);
#endif /* CONFIG_PLAT_EXYNOS5410 */

    /* Load system images */
    printf("Loading Linux: \'%s\' dtb: \'%s\'\n", VM_LINUX_NAME, VM_LINUX_DTB_NAME);
    err = load_linux(&vm, VM_LINUX_NAME, VM_LINUX_DTB_NAME);
    if (err) {
        printf("Failed to load VM image\n");
        seL4_DebugHalt();
        return -1;
    }

#ifdef CONFIG_VM_VCHAN
    vm_vchan_setup(&vm);
#endif //CONFIG_VM_VCHAN

    /* Power on */
    printf("Starting VM\n\n");
    err = vm_start(&vm);
    if (err) {
        printf("Failed to start VM\n");
        seL4_DebugHalt();
        return -1;
    }

    /* Loop forever, handling events */
    while (1) {
        seL4_MessageInfo_t tag;
        seL4_Word sender_badge;

        tag = seL4_Recv(_fault_endpoint, &sender_badge);
        if (sender_badge == 0) {
            seL4_Word label;
            label = seL4_MessageInfo_get_label(tag);
            if (label == IRQ_MESSAGE_LABEL) {
                irq_server_handle_irq_ipc(_irq_server);
            } else {
                printf("Unknown label (%d) for IPC badge %d\n", label, sender_badge);
            }
        } else if (sender_badge == VUSB_NBADGE) {
            vusb_notify();
        } else {
            assert(sender_badge == VM_BADGE);
            err = vm_event(&vm, tag);
            if (err) {
                /* Shutdown */
                vm_stop(&vm);
                seL4_DebugHalt();
                while (1);
            }
        }
    }

    return 0;
}

/* base_prio is an optional attribute of the VM component. */
extern const int __attribute__((weak)) base_prio;

int 
run(void) {
    /* if the base_prio attribute is set, use it */
    if (&base_prio != NULL) {
       VM_PRIO = base_prio;
    }
    return main_continued();
}


/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include <autoconf.h>

#ifdef CONFIG_VM_VCHAN
#include <sel4vchan/vmm_manager.h>
#include <sel4vchan/vchan_copy.h>
#include <sel4vchan/vchan_sharemem.h>
#include <sel4vchan/libvchan.h>
#include <sel4vchan/vchan_component.h>

#include <sel4arm-vmm/vchan_vm_component.h>

#include <VM.h>

#include "cmks_vchan_vm.h"

#define VM_VCHAN_OUTPUT_LVL 1

#define DVMVCHAN(lvl, ...) \
    do{ if(lvl >= 1 && lvl <= VM_VCHAN_OUTPUT_LVL){ \
        printf("vchan-vmside::%d: %s:%d | ", lvl, __func__, __LINE__); \
        printf(__VA_ARGS__); \
    } }while(0) \
        /*  */

static int driver_connect(void *data, uint64_t cmd);

static int vchan_connect(void *data, uint64_t cmd);
static int vchan_close(void *data, uint64_t cmd);
static int vchan_buf_state(void *data, uint64_t cmd);
static int vchan_readwrite(void *data, uint64_t cmd);
static int vchan_state(void *data, uint64_t cmd);

static void vchan_callback(void *addr);
static void vchan_ack(void* token);

/* Function lookup table for handling requests */
static struct vmm_manager_ops {
    int (*op_func[NUM_VMM_OPS])(void *, uint64_t);
} vmm_manager_ops_table = {
    .op_func[VMM_CONNECT]           =   &driver_connect,
    .op_func[SEL4_VCHAN_CONNECT]    =   &vchan_connect,
    .op_func[SEL4_VCHAN_CLOSE]      =   &vchan_close,
    .op_func[VCHAN_SEND]            =   &vchan_readwrite,
    .op_func[VCHAN_RECV]            =   &vchan_readwrite,
    .op_func[SEL4_VCHAN_STATE]      =   &vchan_state,
};

static vm_t *run_vmm;
static char driver_arg[1024];
static bool driver_connected = 0;
static virq_handle_t vchan_irq_handle;

typedef struct vchan_alert_internal {
    vchan_alert_t stats;
    uintptr_t out_addr;
} vchan_alert_internal_t;

/* vchan connection definition */
static camkes_vchan_con_t vchan_camkes_component = {
    .connect = &vchan_con_new_connection,
    .disconnect = &vchan_con_rem_connection,
    .get_buf = &vchan_con_get_buf,
    .status = &vchan_con_status,
    .alert_status = &vchan_con_data_stats,
    .reg_callback = &vevent_reg_callback,
    .alert = &vchan_con_ping,

    .dest_dom_number = 50,
    .source_dom_number = 0,
};

/* Set up relevent runtime systems for vchan */
void vm_vchan_setup(vm_t *vm) {
    vm->lock = &vm_lock_lock;
    vm->unlock = &vm_lock_unlock;

    vchan_irq_handle = vm_virq_new(vm, VCHAN_EVENT_IRQ, &vchan_ack, NULL);
    reg_new_vchan_con(vm, &vchan_camkes_component);
    vchan_camkes_component.data_buf = (void *)share_mem;
}

/* No ack callback needed when the vchan acknoledges a vchan irq */
static void vchan_ack(void* token) {}


static int update_callback_alert(void *addr) {
    int res;
    vchan_alert_internal_t *pass = addr;
    vchan_alert_t *alrt = (vchan_alert_t *) &(pass->stats);

    camkes_vchan_con_t *con = get_vchan_con(run_vmm, alrt->dest);
    if(con == NULL) {
        DVMVCHAN(2, "vchan-cb: No vchan component instance for %d\n", alrt->dest);
        return -1;
    }

    vchan_ctrl_t ct = {
        .domain = con->source_dom_number,
        .dest = alrt->dest,
        .port = alrt->port,
    };

    res = con->alert_status(ct, &(alrt->data_ready), &(alrt->buffer_space));

    DVMVCHAN(2, "vchan-cb: |%d|%d|%d|%d|%d\n",
        alrt->dest, alrt->port, alrt->buffer_space, alrt->data_ready);

    if(res != -1) {
        if(res == 1) {
            DVMVCHAN(2, "vchan-cb: client side closed, cb %d\n", alrt->port);
            free(pass);
        } else {
            vm_copyout(run_vmm, alrt, pass->out_addr, sizeof(vchan_alert_t));
            con->reg_callback(&vchan_callback, addr);
        }
    } else {
        DVMVCHAN(2, "vchan-cb: getting status failed\n");
    }

    return res;
}

/*
    Callback function that is fired when a vchan event is emitted
        The nature of the event (a full or empty data buffer), is passed to the running vm
            via coping the event value and triggering a hardware IRQ
*/
static void vchan_callback(void *addr) {
    DVMVCHAN(5, "vchan-cb: triggered\n");

    update_callback_alert(addr);
    vm_inject_IRQ(vchan_irq_handle);

    DVMVCHAN(5, "vchan-cb: concluded\n");
}

/*
    Return the given vm guest number of this component
*/
int get_vm_num() {
    int res;
    // char *name = (char *) get_instance_name();
    int ret = sscanf("vm_vm0", "vm_vm%d", &res);
    if(ret == 0) {
        return -1;
    }

    return res;
}

/*
    Return the state of a given vchan connection
*/
static int vchan_state(void *data, uint64_t cmd) {
    vchan_check_args_t *args = data;
    camkes_vchan_con_t *con = get_vchan_con(run_vmm, args->v.dest);
    if(con == NULL) {
        DVMVCHAN(2, "connect: %d, has no vchan component instance\n", args->v.domain);
        return -1;
    }

    args->state = con->status(args->v);
    return 0;
}

/*
    Connect a vchan to a another guest vm
*/
static int vchan_connect(void *data, uint64_t cmd) {
    int res;
    vchan_connect_t *pass = data;

    DVMVCHAN(2, "connect: %d, connecting to %d\n", pass->v.domain, pass->v.dest);

    camkes_vchan_con_t *con = get_vchan_con(run_vmm, pass->v.dest);
    if(con == NULL) {
        DVMVCHAN(2, "connect: %d, has no vchan component instance\n", pass->v.domain);
        return -1;
    }

    vchan_alert_internal_t *alrt = malloc(sizeof(vchan_alert_internal_t));
    if(pass == NULL) {
        DVMVCHAN(2, "connect: %d, failed to allocate internal vchan-alert\n", pass->v.domain);
        return -1;
    }

    vchan_connect_t t = {
        .v.domain = con->source_dom_number,
        .v.dest = pass->v.dest,
        .v.port = pass->v.port,
        .server = pass->server,
    };

    res = con->connect(t);
    if(res < 0) {
        DVMVCHAN(2, "connect: %d, failed to connect to %d\n", pass->v.domain, pass->v.dest);
        return -1;
    }

    DVMVCHAN(2, "connect: registering cb\n");
    alrt->out_addr = pass->event_mon;
    vm_copyin(run_vmm, &(alrt->stats), (uintptr_t) pass->event_mon, sizeof(vchan_alert_t));

    if(update_callback_alert((void *) alrt) < 0) {
        DVMVCHAN(2, "connect: %d, failed reg callback\n", pass->v.domain);
        return -1;
    }

    DVMVCHAN(2, "connect: Existing buffer stats: %d . %d\n", alrt->stats.buffer_space, alrt->stats.data_ready);
    con->alert();

    return 0;
}

/*
    Close a vchan connection this guest vm is using
*/
static int vchan_close(void *data, uint64_t cmd) {
    vchan_connect_t *pass = data;

    camkes_vchan_con_t *con = get_vchan_con(run_vmm, pass->v.dest);
    if(con == NULL) {
        DVMVCHAN(2, "close: %d, has no vchan component instance\n", pass->v.domain);
        return -1;
    }

    vchan_connect_t t = {
        .v.domain = con->source_dom_number,
        .v.dest = pass->v.dest,
        .v.port = pass->v.port,
        .server = pass->server,
    };

    con->disconnect(t);
    con->alert();

    return 0;
}


/*
    Function for sending/recieving data from other vm's
        Copies into a memory buffer, and then defers to VmmManager to finish the operation
        Defering is necessary for ensuring concurrency
*/
static int vchan_readwrite(void *data, uint64_t cmd) {
    vchan_args_t *args = data;
    int *update;

    DVMVCHAN(4, "vmcall_readwrite: starting action %d\n", (int) cmd);

    camkes_vchan_con_t *con = get_vchan_con(run_vmm, args->v.dest);
    if(con == NULL) {
        DVMVCHAN(2, "vmcall_readwrite: %d, has no vchan component instance\n", args->v.domain);
        return -1;
    }

    size_t size = args->size;
    uintptr_t phys = args->mmap_phys_ptr;

    vchan_ctrl_t bargs = {
        .domain = con->source_dom_number,
        .dest = args->v.dest,
        .port = args->v.port,
    };

    /* Perfom copy of data to appropriate destination */
    vchan_buf_t *b = get_vchan_buf(&bargs, con, cmd);
    assert(b != NULL);
    size_t filled = abs(b->write_pos - b->read_pos);

    /*
        If streaming, send as much data as possible
         If not streaming, any operation that can't fit into the buffer fails
    */
    if(cmd == VCHAN_RECV) {
        if(args->stream) {
            size = MIN(filled, args->size);
        } else if(filled < args->size) {
            DVMVCHAN(2, "vmcall_readwrite: bad recv size |rq:%d|hv:%d|\n", args->size, filled);
            return -1;
        }
    } else {
        if(args->stream) {
            size = MIN(VCHAN_BUF_SIZE - filled, args->size);
        } else if ((VCHAN_BUF_SIZE - filled) < args->size) {
            DVMVCHAN(2, "vmcall_readwrite: bad send size |rq:%d|hv:%d|\n",
                     (int) args->size, (int) (VCHAN_BUF_SIZE - filled));
            return -1;
        }
    }

    off_t remain = 0;

    if(size != 0) {
        if(cmd == VCHAN_SEND) {
            update = &(b->write_pos);
        } else {
            update = &(b->read_pos);
        }

        off_t start = (*update % VCHAN_BUF_SIZE);
        if(start + size > VCHAN_BUF_SIZE) {
            remain = (start + size) - VCHAN_BUF_SIZE;
            size -= remain;
        }

        if(cmd == VCHAN_SEND) {
            vm_copyin(run_vmm, (b->sync_data + start), phys, size);
            vm_copyin(run_vmm, (b->sync_data), (phys + size), remain);
        } else {
            vm_copyout(run_vmm, (b->sync_data + start), phys, size);
            vm_copyout(run_vmm, (b->sync_data), (phys + size), remain);
        }

        *update += (size + remain);
        DVMVCHAN(5, "vmcall_readwrite: finished action %d | %d | %d\n", (int) cmd, size, (int) remain);
    }

    args->size = (size + remain);
    con->alert();

    return 0;
}

/*
    Used for replying back to a driver successfully connecting
*/
static int driver_connect(void *data, uint64_t cmd) {
    /* Only allow one vchan driver instance to be connected */
    if(driver_connected)
        return -1;

    struct vmm_args *vargs = data;
    driver_connected = 1;
    vargs->datatype = DATATYPE_INT;
    int *res = (int *)vargs->ret_data;
    *res = get_vm_num();
    if(*res < 0) {
        return -1;
    }

    return 0;
}

/*
    Entry point for vchan calls in the hypervisor
        Determine and perform a given command
*/
void vchan_entry_point(vm_t *vm, uint32_t data) {
    char args_buffer[256];
    run_vmm = vm;
    int cmd;

    DVMVCHAN(4, "entry: in call\n");

    vm_copyin(vm, &args_buffer, data, sizeof(vmcall_args_t));
    vmcall_args_t *args = (vmcall_args_t *)args_buffer;
    cmd = args->cmd;

    /* Catch if the request is for an invalid command */
    if(cmd >= NUM_VMM_OPS || vmm_manager_ops_table.op_func[cmd] == NULL) {
        DVMVCHAN(2, "vchan: unsupported command or null tbl arg %d\n", cmd);
        args->err = -1;
    } else {
        /* Perform given token:command action */
        vm_copyin(vm, &driver_arg, args->phys_data, args->size);
        args->err = (*vmm_manager_ops_table.op_func[cmd])(&driver_arg, cmd);
        if(args->err != -1) {
            vm_copyout(vm, &driver_arg, args->phys_data, args->size);
        }
    }
    vm_copyout(vm, &args_buffer, data, sizeof(vmcall_args_t));
    DVMVCHAN(4, "entry: returning from call with |%d|\n", cmd);
}
#endif //CONFIG_VM_VCHAN

/*
* Copyright 2017, Data61
* Commonwealth Scientific and Industrial Research Organisation (CSIRO)
* ABN 41 687 119 230.
*
* This software may be distributed and modified according to the terms of
* the BSD 2-Clause license. Note that NO WARRANTY is provided.
* See "LICENSE_BSD2.txt" for details.
*
* @TAG(D61_BSD)
*/

#include <stdio.h>

#include <camkes.h>

#define ALL_ZERO 0x0
#define ALL_ONE 0xFFFFFFFF

/* Mask to apply.  Currently everything in UARTD device is allowed */
uint32_t uart_mask_registers[] = {
    ALL_ONE, // 0x0 UART_THR_DLAB_0_0
    ALL_ONE, // 0x4 UART_IER_DLAB_0_0
    ALL_ONE, // 0x8 UART_IIR_FCR_0
    ALL_ONE, // 0xc UART_LCR_0
    ALL_ONE, // 0x10 UART_MCR_0
    ALL_ONE, // 0x14 UART_LSR_0
    ALL_ONE, // 0x18 UART_MSR_0
    ALL_ONE, // 0x1c UART_SPR_0
    ALL_ONE, // 0x20 UART_IRDA_CSR_0
    ALL_ONE, // 0x24 UART_RX_FIFO_CFG_0
    ALL_ONE, // 0x28 UART_MIE_0
    ALL_ONE, // 0x2c Reserved
    ALL_ONE, // 0x30 Reserved
    ALL_ONE, // 0x34 Reserved
    ALL_ONE, // 0x38
    ALL_ONE, // 0x3c UART_ASR_0
};

struct access_mask {
    uint32_t start;
    uint32_t size;
    uint32_t *mask;
};

struct access_mask uart_mask = {
    .start = 0x300,
    .size = 0x40,
    .mask = uart_mask_registers,
};


void gen_fwd__init() {
    ZF_LOGI("Init uart forward access control interface");
}

/**
 * Return value at offset `addr` in the UART device frame.
 * Only allows addresses within the UARTD region
 * Value is masked before being returned.
 *
 * @param  addr offset into frame.  Must be < PAGE_SIZE
 * @return      Masked value at hardware address
 */
uint32_t gen_fwd_read(size_t addr) {

    if (addr >= PAGE_SIZE) {
        ZF_LOGE("Invalid address given: 0x%08x\n", addr);
        return 0;
    }
    uint8_t *base_addr = (uint8_t *)tk1_uart_regs;
    uint32_t *update = (uint32_t *)(base_addr + addr);
    if (addr >= uart_mask.start && addr < (uart_mask.start + uart_mask.size)) {
        uint32_t index = (addr - uart_mask.start)/4;
        uint32_t mask = uart_mask.mask[index];
        return (*update & mask);
    } else {
        ZF_LOGE("INVALID DATA READ: 0x%08x\n", addr);
        return 0;
    }

}

/**
 * Writes `value` to offset `addr` in the UART device frame.
 * Only allows addresses within the UARTD region
 * Value is masked before being written.
 *
 * @param  addr offset into frame.  Must be < PAGE_SIZE
 * @param  value value to write.  Value is masked before writing.
 */
void gen_fwd_write(size_t addr, uint32_t value) {
    if (addr >= PAGE_SIZE) {
        ZF_LOGE("Invalid address given");
        return;
    }

    uint8_t *base_addr = (uint8_t *)tk1_uart_regs;
    uint32_t *update = (uint32_t *)(base_addr + addr);
    if (addr >= uart_mask.start && addr < (uart_mask.start + uart_mask.size)) {
        uint32_t index = (addr - uart_mask.start)/sizeof(uint32_t);
        uint32_t mask = uart_mask.mask[index];
        *update = (*update & ~(mask)) | (value & mask);
    } else {
        ZF_LOGE("INVALID DATA WRITE: 0x%08x, Value: 0x%08x\n", addr, value);
        return;
    }
}

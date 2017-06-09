/*
 * Copyright 2016, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 * @TAG(D61_BSD)
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>

#define SPI_TRANS_MAX_SIZE    255

/* SPI Application IDs*/
#define CLIENT_APP_ID  0
#define CAN_APP_ID     1
#define NUM_APPS       2


typedef struct spi_buf {
    uint8_t txbuf[SPI_TRANS_MAX_SIZE];
    uint8_t rxbuf[SPI_TRANS_MAX_SIZE];
    volatile bool lock;                    //shared buffer lock
} spi_dev_port_t;

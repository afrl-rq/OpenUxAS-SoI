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

#include <stdint.h>

#define CAN_SID_BITS  11
#define CAN_EID_BITS  18
#define CAN_EID_MASK  0x3FFFFU

#define CAN_MAX_DLC   8

/**
 * Transmission Priority
 */
typedef enum can_frame_priority {
    LOW = 0,
    MED_LOW,
    MED_HIGH,
    HIGH
} can_frame_priority_t;

/**
 * TX Buffer Status
 */
typedef enum can_txb_status {
    IDLE = 0,
    PENDING,
    LOST,
    ERR,
    ABORT
} can_txb_status_t;

/** CAN Arbitration Field
 *
 * @id: CAN id(11 bits for standard frame, 29 bits if extended frame).
 * @exide: Extended frame flag.
 * @rtr: Remote Transmission Request.
 * @err: Error frame flag.
 */
struct can_id {
    uint32_t id: 29;
    uint32_t exide: 1;
    uint32_t rtr: 1;
    uint32_t err: 1;
};
typedef struct can_id can_id_t;



/**
 * Basic CAN frame structure.
 *
 * @ident: Identifier.
 * @prio: Transmit priority.
 * @dlc: Data Length Code(0 ~ 8).
 * @data: frame payload(8 bytes maximum).
 *
 * NOTE: The priority is MCP2515 only, it is not related to any prioritization
 *       implicit in the CAN protocol.
 */
struct can_frame {
    struct can_id ident;
    uint8_t prio: 2;
    uint8_t dlc: 4;
    uint8_t data[CAN_MAX_DLC] __attribute__((aligned(8)));
};
typedef struct can_frame can_frame_t;

/**
 * CAN RX buffer filter.
 *
 * @id: CAN frame identifier bits which are accepted.
 * @mask: CAN mask.
 */
struct can_filter {
    uint32_t id;
    uint32_t mask;
};
typedef struct can_filter can_filter_t;

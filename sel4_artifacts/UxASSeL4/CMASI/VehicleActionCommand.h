
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VehicleAction.h"
#include "enums.h"
#define LMCP_VehicleActionCommand_SUB "afrl.cmasi.VehicleActionCommand"

#define LMCP_VehicleActionCommand_TYPENAME "VehicleActionCommand"

#define LMCP_VehicleActionCommand_TYPE 47

typedef struct {
    lmcp_object super;
    int64_t CommandID;

// Units: None
    int64_t VehicleID;

    VehicleAction** VehicleActionList;
    array_info VehicleActionList_ai;

    CommandStatusType Status;

} VehicleActionCommand;
void lmcp_pp_VehicleActionCommand(VehicleActionCommand* s);
size_t lmcp_packsize_VehicleActionCommand (VehicleActionCommand* i);
size_t lmcp_pack_VehicleActionCommand_header(uint8_t* buf, VehicleActionCommand* i);
void lmcp_free_VehicleActionCommand(VehicleActionCommand* i, int out_malloced);
void lmcp_init_VehicleActionCommand (VehicleActionCommand** i);
int lmcp_unpack_VehicleActionCommand(uint8_t** buf, size_t *size_remain,VehicleActionCommand* outp);
size_t lmcp_pack_VehicleActionCommand(uint8_t* buf, VehicleActionCommand* i);

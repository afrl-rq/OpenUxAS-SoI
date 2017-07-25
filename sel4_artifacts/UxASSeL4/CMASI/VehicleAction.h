
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_VehicleAction_SUB "afrl.cmasi.VehicleAction"

#define LMCP_VehicleAction_TYPENAME "VehicleAction"

#define LMCP_VehicleAction_TYPE 7

typedef struct {
    lmcp_object super;
    int64_t* AssociatedTaskList;
    array_info AssociatedTaskList_ai;

} VehicleAction;
void lmcp_pp_VehicleAction(VehicleAction* s);
size_t lmcp_packsize_VehicleAction (VehicleAction* i);
size_t lmcp_pack_VehicleAction_header(uint8_t* buf, VehicleAction* i);
void lmcp_free_VehicleAction(VehicleAction* i, int out_malloced);
void lmcp_init_VehicleAction (VehicleAction** i);
int lmcp_unpack_VehicleAction(uint8_t** buf, size_t *size_remain,VehicleAction* outp);
size_t lmcp_pack_VehicleAction(uint8_t* buf, VehicleAction* i);

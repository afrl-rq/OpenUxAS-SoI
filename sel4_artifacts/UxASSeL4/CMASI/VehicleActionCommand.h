
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VehicleAction.h"
#include "enums.h"
#define LMCP_VehicleActionCommand_SUB "afrl.cmasi.VehicleActionCommand"

#define LMCP_VehicleActionCommand_TYPENAME "VehicleActionCommand"

#define LMCP_VehicleActionCommand_TYPE 47

struct VehicleActionCommand_struct {
    lmcp_object super;
    int64_t commandid;

// Units: None
    int64_t vehicleid;

    VehicleAction** vehicleactionlist;
    array_info vehicleactionlist_ai;

    CommandStatusType status;

};
typedef struct VehicleActionCommand_struct VehicleActionCommand;
void lmcp_pp_VehicleActionCommand(VehicleActionCommand* s);
size_t lmcp_packsize_VehicleActionCommand (VehicleActionCommand* i);
size_t lmcp_pack_VehicleActionCommand_header(uint8_t* buf, VehicleActionCommand* i);
void lmcp_free_VehicleActionCommand(VehicleActionCommand* i, int out_malloced);
void lmcp_init_VehicleActionCommand (VehicleActionCommand** i);
int lmcp_unpack_VehicleActionCommand(uint8_t** buf, size_t *size_remain,VehicleActionCommand* outp);
size_t lmcp_pack_VehicleActionCommand(uint8_t* buf, VehicleActionCommand* i);

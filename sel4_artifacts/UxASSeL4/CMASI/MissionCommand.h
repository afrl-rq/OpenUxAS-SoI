
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VehicleActionCommand.h"
#include "Waypoint.h"
#define LMCP_MissionCommand_SUB "afrl.cmasi.MissionCommand"

#define LMCP_MissionCommand_TYPENAME "MissionCommand"

#define LMCP_MissionCommand_TYPE 36

struct MissionCommand_struct {
    VehicleActionCommand super;
// Units: None
    Waypoint ** waypointlist;
    array_info waypointlist_ai;

    int64_t firstwaypoint;

};
typedef struct MissionCommand_struct MissionCommand;
void lmcp_pp_MissionCommand(MissionCommand* s);
size_t lmcp_packsize_MissionCommand (MissionCommand* i);
size_t lmcp_pack_MissionCommand_header(uint8_t* buf, MissionCommand* i);
void lmcp_free_MissionCommand(MissionCommand* i, int out_malloced);
void lmcp_init_MissionCommand (MissionCommand** i);
int lmcp_unpack_MissionCommand(uint8_t** buf, size_t *size_remain,MissionCommand* outp);
size_t lmcp_pack_MissionCommand(uint8_t* buf, MissionCommand* i);

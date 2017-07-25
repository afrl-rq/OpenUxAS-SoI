
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VehicleActionCommand.h"
#include "PathWaypoint.h"
#include "enums.h"
#define LMCP_FollowPathCommand_SUB "afrl.cmasi.FollowPathCommand"

#define LMCP_FollowPathCommand_TYPENAME "FollowPathCommand"

#define LMCP_FollowPathCommand_TYPE 56

typedef struct {
    VehicleActionCommand super;
    int64_t FirstWaypoint;

    PathWaypoint** WaypointList;
    array_info WaypointList_ai;

// Units: milliseconds
    int64_t StartTime;

// Units: milliseconds
    int64_t StopTime;

    TravelMode RepeatMode;

} FollowPathCommand;
void lmcp_pp_FollowPathCommand(FollowPathCommand* s);
size_t lmcp_packsize_FollowPathCommand (FollowPathCommand* i);
size_t lmcp_pack_FollowPathCommand_header(uint8_t* buf, FollowPathCommand* i);
void lmcp_free_FollowPathCommand(FollowPathCommand* i, int out_malloced);
void lmcp_init_FollowPathCommand (FollowPathCommand** i);
int lmcp_unpack_FollowPathCommand(uint8_t** buf, size_t *size_remain,FollowPathCommand* outp);
size_t lmcp_pack_FollowPathCommand(uint8_t* buf, FollowPathCommand* i);

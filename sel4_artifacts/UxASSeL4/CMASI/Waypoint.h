
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Location3D.h"
#include "enums.h"
#include "VehicleAction.h"
#define LMCP_Waypoint_SUB "afrl.cmasi.Waypoint"

#define LMCP_Waypoint_TYPENAME "Waypoint"

#define LMCP_Waypoint_TYPE 35

typedef struct {
    Location3D super;
// Units: None
    int64_t Number;

// Units: None
    int64_t NextWaypoint;

// Units: meter/sec
    float Speed;

    SpeedType SpeedType;

// Units: meter/sec
    float ClimbRate;

    TurnType TurnType;

// Units: None
    VehicleAction** VehicleActionList;
    array_info VehicleActionList_ai;

    int64_t ContingencyWaypointA;

    int64_t ContingencyWaypointB;

    int64_t* AssociatedTasks;
    array_info AssociatedTasks_ai;

} Waypoint;
void lmcp_pp_Waypoint(Waypoint* s);
size_t lmcp_packsize_Waypoint (Waypoint* i);
size_t lmcp_pack_Waypoint_header(uint8_t* buf, Waypoint* i);
void lmcp_free_Waypoint(Waypoint* i, int out_malloced);
void lmcp_init_Waypoint (Waypoint** i);
int lmcp_unpack_Waypoint(uint8_t** buf, size_t *size_remain,Waypoint* outp);
size_t lmcp_pack_Waypoint(uint8_t* buf, Waypoint* i);

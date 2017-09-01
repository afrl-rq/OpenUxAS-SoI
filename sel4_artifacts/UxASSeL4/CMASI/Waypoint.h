
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Location3D.h"
#include "enums.h"
#include "VehicleAction.h"
#define LMCP_Waypoint_SUB "afrl.cmasi.Waypoint"

#define LMCP_Waypoint_TYPENAME "Waypoint"

#define LMCP_Waypoint_TYPE 35

struct Waypoint_struct {
    Location3D super;
// Units: None
    int64_t number;

// Units: None
    int64_t nextwaypoint;

// Units: meter/sec
    uint32_t speed;

    SpeedType speedtype;

// Units: meter/sec
    uint32_t climbrate;

    TurnType turntype;

// Units: None
    VehicleAction** vehicleactionlist;
    array_info vehicleactionlist_ai;

    int64_t contingencywaypointa;

    int64_t contingencywaypointb;

    int64_t* associatedtasks;
    array_info associatedtasks_ai;

};
typedef struct Waypoint_struct Waypoint;
void lmcp_pp_Waypoint(Waypoint* s);
size_t lmcp_packsize_Waypoint (Waypoint* i);
size_t lmcp_pack_Waypoint_header(uint8_t* buf, Waypoint* i);
void lmcp_free_Waypoint(Waypoint* i, int out_malloced);
void lmcp_init_Waypoint (Waypoint** i);
int lmcp_unpack_Waypoint(uint8_t** buf, size_t *size_remain,Waypoint* outp);
size_t lmcp_pack_Waypoint(uint8_t* buf, Waypoint* i);

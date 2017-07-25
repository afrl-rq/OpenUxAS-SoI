
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Waypoint.h"
#define LMCP_PathWaypoint_SUB "afrl.cmasi.PathWaypoint"

#define LMCP_PathWaypoint_TYPENAME "PathWaypoint"

#define LMCP_PathWaypoint_TYPE 57

typedef struct {
    Waypoint super;
// Units: milliseconds
    int64_t PauseTime;

} PathWaypoint;
void lmcp_pp_PathWaypoint(PathWaypoint* s);
size_t lmcp_packsize_PathWaypoint (PathWaypoint* i);
size_t lmcp_pack_PathWaypoint_header(uint8_t* buf, PathWaypoint* i);
void lmcp_free_PathWaypoint(PathWaypoint* i, int out_malloced);
void lmcp_init_PathWaypoint (PathWaypoint** i);
int lmcp_unpack_PathWaypoint(uint8_t** buf, size_t *size_remain,PathWaypoint* outp);
size_t lmcp_pack_PathWaypoint(uint8_t* buf, PathWaypoint* i);


#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Waypoint.h"
#include "enums.h"
#define LMCP_WaypointTransfer_SUB "afrl.cmasi.WaypointTransfer"

#define LMCP_WaypointTransfer_TYPENAME "WaypointTransfer"

#define LMCP_WaypointTransfer_TYPE 59

typedef struct {
    lmcp_object super;
    int64_t EntityID;

    Waypoint** Waypoints;
    array_info Waypoints_ai;

    WaypointTransferMode TransferMode;

} WaypointTransfer;
void lmcp_pp_WaypointTransfer(WaypointTransfer* s);
size_t lmcp_packsize_WaypointTransfer (WaypointTransfer* i);
size_t lmcp_pack_WaypointTransfer_header(uint8_t* buf, WaypointTransfer* i);
void lmcp_free_WaypointTransfer(WaypointTransfer* i, int out_malloced);
void lmcp_init_WaypointTransfer (WaypointTransfer** i);
int lmcp_unpack_WaypointTransfer(uint8_t** buf, size_t *size_remain,WaypointTransfer* outp);
size_t lmcp_pack_WaypointTransfer(uint8_t* buf, WaypointTransfer* i);


#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "NavigationAction.h"
#define LMCP_GoToWaypointAction_SUB "afrl.cmasi.GoToWaypointAction"

#define LMCP_GoToWaypointAction_TYPENAME "GoToWaypointAction"

#define LMCP_GoToWaypointAction_TYPE 28

typedef struct {
    NavigationAction super;
    int64_t WaypointNumber;

} GoToWaypointAction;
void lmcp_pp_GoToWaypointAction(GoToWaypointAction* s);
size_t lmcp_packsize_GoToWaypointAction (GoToWaypointAction* i);
size_t lmcp_pack_GoToWaypointAction_header(uint8_t* buf, GoToWaypointAction* i);
void lmcp_free_GoToWaypointAction(GoToWaypointAction* i, int out_malloced);
void lmcp_init_GoToWaypointAction (GoToWaypointAction** i);
int lmcp_unpack_GoToWaypointAction(uint8_t** buf, size_t *size_remain,GoToWaypointAction* outp);
size_t lmcp_pack_GoToWaypointAction(uint8_t* buf, GoToWaypointAction* i);

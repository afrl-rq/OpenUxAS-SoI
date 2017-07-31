
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VehicleAction.h"
#include "Location3D.h"
#define LMCP_StopMovementAction_SUB "afrl.cmasi.StopMovementAction"

#define LMCP_StopMovementAction_TYPENAME "StopMovementAction"

#define LMCP_StopMovementAction_TYPE 58

typedef struct {
    VehicleAction super;
    Location3D* Location;

} StopMovementAction;
void lmcp_pp_StopMovementAction(StopMovementAction* s);
size_t lmcp_packsize_StopMovementAction (StopMovementAction* i);
size_t lmcp_pack_StopMovementAction_header(uint8_t* buf, StopMovementAction* i);
void lmcp_free_StopMovementAction(StopMovementAction* i, int out_malloced);
void lmcp_init_StopMovementAction (StopMovementAction** i);
int lmcp_unpack_StopMovementAction(uint8_t** buf, size_t *size_remain,StopMovementAction* outp);
size_t lmcp_pack_StopMovementAction(uint8_t* buf, StopMovementAction* i);

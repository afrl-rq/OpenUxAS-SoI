
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VehicleAction.h"
#define LMCP_NavigationAction_SUB "afrl.cmasi.NavigationAction"

#define LMCP_NavigationAction_TYPENAME "NavigationAction"

#define LMCP_NavigationAction_TYPE 32

typedef struct {
    VehicleAction super;
} NavigationAction;
void lmcp_pp_NavigationAction(NavigationAction* s);
size_t lmcp_packsize_NavigationAction (NavigationAction* i);
size_t lmcp_pack_NavigationAction_header(uint8_t* buf, NavigationAction* i);
void lmcp_free_NavigationAction(NavigationAction* i, int out_malloced);
void lmcp_init_NavigationAction (NavigationAction** i);
int lmcp_unpack_NavigationAction(uint8_t** buf, size_t *size_remain,NavigationAction* outp);
size_t lmcp_pack_NavigationAction(uint8_t* buf, NavigationAction* i);


#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "NavigationAction.h"
#include "enums.h"
#include "Location3D.h"
#define LMCP_LoiterAction_SUB "afrl.cmasi.LoiterAction"

#define LMCP_LoiterAction_TYPENAME "LoiterAction"

#define LMCP_LoiterAction_TYPE 33

typedef struct {
    NavigationAction super;
// Units: none
    LoiterType LoiterType;

// Units: meter
    float Radius;

// Units: degree
    float Axis;

// Units: meter
    float Length;

// Units: None
    LoiterDirection Direction;

// Units: milliseconds
    int64_t Duration;

// Units: meter/sec
    float Airspeed;

    Location3D* Location;

} LoiterAction;
void lmcp_pp_LoiterAction(LoiterAction* s);
size_t lmcp_packsize_LoiterAction (LoiterAction* i);
size_t lmcp_pack_LoiterAction_header(uint8_t* buf, LoiterAction* i);
void lmcp_free_LoiterAction(LoiterAction* i, int out_malloced);
void lmcp_init_LoiterAction (LoiterAction** i);
int lmcp_unpack_LoiterAction(uint8_t** buf, size_t *size_remain,LoiterAction* outp);
size_t lmcp_pack_LoiterAction(uint8_t* buf, LoiterAction* i);

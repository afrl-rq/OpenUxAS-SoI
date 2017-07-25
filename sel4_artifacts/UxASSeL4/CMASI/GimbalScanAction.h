
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadAction.h"
#define LMCP_GimbalScanAction_SUB "afrl.cmasi.GimbalScanAction"

#define LMCP_GimbalScanAction_TYPENAME "GimbalScanAction"

#define LMCP_GimbalScanAction_TYPE 25

typedef struct {
    PayloadAction super;
// Units: degree/second
    float AzimuthSlewRate;

// Units: degree/second
    float ElevationSlewRate;

// Units: degree
    float StartAzimuth;

// Units: degree
    float EndAzimuth;

// Units: degree
    float StartElevation;

// Units: degree
    float EndElevation;

    uint32_t Cycles;

} GimbalScanAction;
void lmcp_pp_GimbalScanAction(GimbalScanAction* s);
size_t lmcp_packsize_GimbalScanAction (GimbalScanAction* i);
size_t lmcp_pack_GimbalScanAction_header(uint8_t* buf, GimbalScanAction* i);
void lmcp_free_GimbalScanAction(GimbalScanAction* i, int out_malloced);
void lmcp_init_GimbalScanAction (GimbalScanAction** i);
int lmcp_unpack_GimbalScanAction(uint8_t** buf, size_t *size_remain,GimbalScanAction* outp);
size_t lmcp_pack_GimbalScanAction(uint8_t* buf, GimbalScanAction* i);

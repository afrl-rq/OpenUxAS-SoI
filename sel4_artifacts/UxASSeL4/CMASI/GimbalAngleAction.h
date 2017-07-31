
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadAction.h"
#define LMCP_GimbalAngleAction_SUB "afrl.cmasi.GimbalAngleAction"

#define LMCP_GimbalAngleAction_TYPENAME "GimbalAngleAction"

#define LMCP_GimbalAngleAction_TYPE 23

typedef struct {
    PayloadAction super;
// Units: degree
    float Azimuth;

// Units: degree
    float Elevation;

// Units: degree
    float Rotation;

} GimbalAngleAction;
void lmcp_pp_GimbalAngleAction(GimbalAngleAction* s);
size_t lmcp_packsize_GimbalAngleAction (GimbalAngleAction* i);
size_t lmcp_pack_GimbalAngleAction_header(uint8_t* buf, GimbalAngleAction* i);
void lmcp_free_GimbalAngleAction(GimbalAngleAction* i, int out_malloced);
void lmcp_init_GimbalAngleAction (GimbalAngleAction** i);
int lmcp_unpack_GimbalAngleAction(uint8_t** buf, size_t *size_remain,GimbalAngleAction* outp);
size_t lmcp_pack_GimbalAngleAction(uint8_t* buf, GimbalAngleAction* i);

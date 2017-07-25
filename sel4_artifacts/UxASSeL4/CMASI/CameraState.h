
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "GimballedPayloadState.h"
#include "Location3D.h"
#include "Location3D.h"
#define LMCP_CameraState_SUB "afrl.cmasi.CameraState"

#define LMCP_CameraState_TYPENAME "CameraState"

#define LMCP_CameraState_TYPE 21

typedef struct {
    GimballedPayloadState super;
// Units: degree
    float HorizontalFieldOfView;

// Units: degree
    float VerticalFieldOfView;

// Units: None
    Location3D** Footprint;
    array_info Footprint_ai;

    Location3D* Centerpoint;

} CameraState;
void lmcp_pp_CameraState(CameraState* s);
size_t lmcp_packsize_CameraState (CameraState* i);
size_t lmcp_pack_CameraState_header(uint8_t* buf, CameraState* i);
void lmcp_free_CameraState(CameraState* i, int out_malloced);
void lmcp_init_CameraState (CameraState** i);
int lmcp_unpack_CameraState(uint8_t** buf, size_t *size_remain,CameraState* outp);
size_t lmcp_pack_CameraState(uint8_t* buf, CameraState* i);


#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadState.h"
#include "enums.h"
#define LMCP_GimballedPayloadState_SUB "afrl.cmasi.GimballedPayloadState"

#define LMCP_GimballedPayloadState_TYPENAME "GimballedPayloadState"

#define LMCP_GimballedPayloadState_TYPE 20

struct GimballedPayloadState_struct {
    PayloadState super;
    GimbalPointingMode pointingmode;

// Units: degree
    uint32_t azimuth;

// Units: degree
    uint32_t elevation;

// Units: degree
    uint32_t rotation;

};
typedef struct GimballedPayloadState_struct GimballedPayloadState;
void lmcp_pp_GimballedPayloadState(GimballedPayloadState* s);
size_t lmcp_packsize_GimballedPayloadState (GimballedPayloadState* i);
size_t lmcp_pack_GimballedPayloadState_header(uint8_t* buf, GimballedPayloadState* i);
void lmcp_free_GimballedPayloadState(GimballedPayloadState* i, int out_malloced);
void lmcp_init_GimballedPayloadState (GimballedPayloadState** i);
int lmcp_unpack_GimballedPayloadState(uint8_t** buf, size_t *size_remain,GimballedPayloadState* outp);
size_t lmcp_pack_GimballedPayloadState(uint8_t* buf, GimballedPayloadState* i);


#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadState.h"
#include "enums.h"
#define LMCP_GimbalState_SUB "afrl.cmasi.GimbalState"

#define LMCP_GimbalState_TYPENAME "GimbalState"

#define LMCP_GimbalState_TYPE 27

struct GimbalState_struct {
    PayloadState super;
// Units: None
    GimbalPointingMode pointingmode;

// Units: degree
    uint32_t azimuth;

// Units: degree
    uint32_t elevation;

// Units: degree
    uint32_t rotation;

};
typedef struct GimbalState_struct GimbalState;
void lmcp_pp_GimbalState(GimbalState* s);
size_t lmcp_packsize_GimbalState (GimbalState* i);
size_t lmcp_pack_GimbalState_header(uint8_t* buf, GimbalState* i);
void lmcp_free_GimbalState(GimbalState* i, int out_malloced);
void lmcp_init_GimbalState (GimbalState** i);
int lmcp_unpack_GimbalState(uint8_t** buf, size_t *size_remain,GimbalState* outp);
size_t lmcp_pack_GimbalState(uint8_t* buf, GimbalState* i);


#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VehicleAction.h"
#define LMCP_VideoStreamAction_SUB "afrl.cmasi.VideoStreamAction"

#define LMCP_VideoStreamAction_TYPENAME "VideoStreamAction"

#define LMCP_VideoStreamAction_TYPE 48

typedef struct {
    VehicleAction super;
// Units: None
    int32_t VideoStreamID;

// Units: None
    int32_t ActiveSensor;

} VideoStreamAction;
void lmcp_pp_VideoStreamAction(VideoStreamAction* s);
size_t lmcp_packsize_VideoStreamAction (VideoStreamAction* i);
size_t lmcp_pack_VideoStreamAction_header(uint8_t* buf, VideoStreamAction* i);
void lmcp_free_VideoStreamAction(VideoStreamAction* i, int out_malloced);
void lmcp_init_VideoStreamAction (VideoStreamAction** i);
int lmcp_unpack_VideoStreamAction(uint8_t** buf, size_t *size_remain,VideoStreamAction* outp);
size_t lmcp_pack_VideoStreamAction(uint8_t* buf, VideoStreamAction* i);


#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadState.h"
#define LMCP_VideoStreamState_SUB "afrl.cmasi.VideoStreamState"

#define LMCP_VideoStreamState_TYPENAME "VideoStreamState"

#define LMCP_VideoStreamState_TYPE 50

typedef struct {
    PayloadState super;
// Units: None
    int64_t ActiveSensor;

} VideoStreamState;
void lmcp_pp_VideoStreamState(VideoStreamState* s);
size_t lmcp_packsize_VideoStreamState (VideoStreamState* i);
size_t lmcp_pack_VideoStreamState_header(uint8_t* buf, VideoStreamState* i);
void lmcp_free_VideoStreamState(VideoStreamState* i, int out_malloced);
void lmcp_init_VideoStreamState (VideoStreamState** i);
int lmcp_unpack_VideoStreamState(uint8_t** buf, size_t *size_remain,VideoStreamState* outp);
size_t lmcp_pack_VideoStreamState(uint8_t* buf, VideoStreamState* i);

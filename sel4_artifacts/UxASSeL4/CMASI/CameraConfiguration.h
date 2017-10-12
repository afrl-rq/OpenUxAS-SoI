
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadConfiguration.h"
#include "enums.h"
#define LMCP_CameraConfiguration_SUB "afrl.cmasi.CameraConfiguration"

#define LMCP_CameraConfiguration_TYPENAME "CameraConfiguration"

#define LMCP_CameraConfiguration_TYPE 19

struct CameraConfiguration_struct {
    PayloadConfiguration super;
    WavelengthBand supportedwavelengthband;

// Units: None
    FOVOperationMode fieldofviewmode;

// Units: degree
    uint32_t minhorizontalfieldofview;

// Units: degree
    uint32_t maxhorizontalfieldofview;

// Units: degree
    uint32_t* discretehorizontalfieldofviewlist;
    array_info discretehorizontalfieldofviewlist_ai;

// Units: pixel
    uint32_t videostreamhorizontalresolution;

// Units: pixel
    uint32_t videostreamverticalresolution;

};
typedef struct CameraConfiguration_struct CameraConfiguration;
void lmcp_pp_CameraConfiguration(CameraConfiguration* s);
size_t lmcp_packsize_CameraConfiguration (CameraConfiguration* i);
size_t lmcp_pack_CameraConfiguration_header(uint8_t* buf, CameraConfiguration* i);
void lmcp_free_CameraConfiguration(CameraConfiguration* i, int out_malloced);
void lmcp_init_CameraConfiguration (CameraConfiguration** i);
int lmcp_unpack_CameraConfiguration(uint8_t** buf, size_t *size_remain,CameraConfiguration* outp);
size_t lmcp_pack_CameraConfiguration(uint8_t* buf, CameraConfiguration* i);

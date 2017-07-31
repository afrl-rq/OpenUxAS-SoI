
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadConfiguration.h"
#include "enums.h"
#define LMCP_CameraConfiguration_SUB "afrl.cmasi.CameraConfiguration"

#define LMCP_CameraConfiguration_TYPENAME "CameraConfiguration"

#define LMCP_CameraConfiguration_TYPE 19

typedef struct {
    PayloadConfiguration super;
    WavelengthBand SupportedWavelengthBand;

// Units: None
    FOVOperationMode FieldOfViewMode;

// Units: degree
    float MinHorizontalFieldOfView;

// Units: degree
    float MaxHorizontalFieldOfView;

// Units: degree
    float* DiscreteHorizontalFieldOfViewList;
    array_info DiscreteHorizontalFieldOfViewList_ai;

// Units: pixel
    uint32_t VideoStreamHorizontalResolution;

// Units: pixel
    uint32_t VideoStreamVerticalResolution;

} CameraConfiguration;
void lmcp_pp_CameraConfiguration(CameraConfiguration* s);
size_t lmcp_packsize_CameraConfiguration (CameraConfiguration* i);
size_t lmcp_pack_CameraConfiguration_header(uint8_t* buf, CameraConfiguration* i);
void lmcp_free_CameraConfiguration(CameraConfiguration* i, int out_malloced);
void lmcp_init_CameraConfiguration (CameraConfiguration** i);
int lmcp_unpack_CameraConfiguration(uint8_t** buf, size_t *size_remain,CameraConfiguration* outp);
size_t lmcp_pack_CameraConfiguration(uint8_t* buf, CameraConfiguration* i);


#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadConfiguration.h"
#include "enums.h"
#define LMCP_GimbalConfiguration_SUB "afrl.cmasi.GimbalConfiguration"

#define LMCP_GimbalConfiguration_TYPENAME "GimbalConfiguration"

#define LMCP_GimbalConfiguration_TYPE 24

typedef struct {
    PayloadConfiguration super;
// Units: None
    GimbalPointingMode* SupportedPointingModes;
    array_info SupportedPointingModes_ai;

// Units: degree
    float MinAzimuth;

// Units: degree
    float MaxAzimuth;

// Units: None
    uint8_t IsAzimuthClamped;

// Units: degree
    float MinElevation;

// Units: degree
    float MaxElevation;

// Units: None
    uint8_t IsElevationClamped;

// Units: degree
    float MinRotation;

// Units: degree
    float MaxRotation;

// Units: None
    uint8_t IsRotationClamped;

// Units: degree/sec
    float MaxAzimuthSlewRate;

// Units: degree/sec
    float MaxElevationSlewRate;

// Units: degree/sec
    float MaxRotationRate;

// Units: None
    int64_t* ContainedPayloadList;
    array_info ContainedPayloadList_ai;

} GimbalConfiguration;
void lmcp_pp_GimbalConfiguration(GimbalConfiguration* s);
size_t lmcp_packsize_GimbalConfiguration (GimbalConfiguration* i);
size_t lmcp_pack_GimbalConfiguration_header(uint8_t* buf, GimbalConfiguration* i);
void lmcp_free_GimbalConfiguration(GimbalConfiguration* i, int out_malloced);
void lmcp_init_GimbalConfiguration (GimbalConfiguration** i);
int lmcp_unpack_GimbalConfiguration(uint8_t** buf, size_t *size_remain,GimbalConfiguration* outp);
size_t lmcp_pack_GimbalConfiguration(uint8_t* buf, GimbalConfiguration* i);

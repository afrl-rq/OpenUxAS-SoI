
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadConfiguration.h"
#include "enums.h"
#define LMCP_GimbalConfiguration_SUB "afrl.cmasi.GimbalConfiguration"

#define LMCP_GimbalConfiguration_TYPENAME "GimbalConfiguration"

#define LMCP_GimbalConfiguration_TYPE 24

struct GimbalConfiguration_struct {
    PayloadConfiguration super;
// Units: None
    GimbalPointingMode* supportedpointingmodes;
    array_info supportedpointingmodes_ai;

// Units: degree
    uint32_t minazimuth;

// Units: degree
    uint32_t maxazimuth;

// Units: None
    uint8_t isazimuthclamped;

// Units: degree
    uint32_t minelevation;

// Units: degree
    uint32_t maxelevation;

// Units: None
    uint8_t iselevationclamped;

// Units: degree
    uint32_t minrotation;

// Units: degree
    uint32_t maxrotation;

// Units: None
    uint8_t isrotationclamped;

// Units: degree/sec
    uint32_t maxazimuthslewrate;

// Units: degree/sec
    uint32_t maxelevationslewrate;

// Units: degree/sec
    uint32_t maxrotationrate;

// Units: None
    int64_t* containedpayloadlist;
    array_info containedpayloadlist_ai;

};
typedef struct GimbalConfiguration_struct GimbalConfiguration;
void lmcp_pp_GimbalConfiguration(GimbalConfiguration* s);
size_t lmcp_packsize_GimbalConfiguration (GimbalConfiguration* i);
size_t lmcp_pack_GimbalConfiguration_header(uint8_t* buf, GimbalConfiguration* i);
void lmcp_free_GimbalConfiguration(GimbalConfiguration* i, int out_malloced);
void lmcp_init_GimbalConfiguration (GimbalConfiguration** i);
int lmcp_unpack_GimbalConfiguration(uint8_t** buf, size_t *size_remain,GimbalConfiguration* outp);
size_t lmcp_pack_GimbalConfiguration(uint8_t* buf, GimbalConfiguration* i);

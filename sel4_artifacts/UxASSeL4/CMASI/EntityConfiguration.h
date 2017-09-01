
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "enums.h"
#include "PayloadConfiguration.h"
#include "KeyValuePair.h"
#define LMCP_EntityConfiguration_SUB "afrl.cmasi.EntityConfiguration"

#define LMCP_EntityConfiguration_TYPENAME "EntityConfiguration"

#define LMCP_EntityConfiguration_TYPE 11

struct EntityConfiguration_struct {
    lmcp_object super;
// Units: None
    int64_t id;

    char* affiliation;
    array_info affiliation_ai;

    char* entitytype;
    array_info entitytype_ai;

    char* label;
    array_info label_ai;

// Units: meter/sec
    uint32_t nominalspeed;

// Units: meter
    uint32_t nominalaltitude;

    AltitudeType nominalaltitudetype;

// Units: None
    PayloadConfiguration** payloadconfigurationlist;
    array_info payloadconfigurationlist_ai;

    KeyValuePair** info;
    array_info info_ai;

};
typedef struct EntityConfiguration_struct EntityConfiguration;
void lmcp_pp_EntityConfiguration(EntityConfiguration* s);
size_t lmcp_packsize_EntityConfiguration (EntityConfiguration* i);
size_t lmcp_pack_EntityConfiguration_header(uint8_t* buf, EntityConfiguration* i);
void lmcp_free_EntityConfiguration(EntityConfiguration* i, int out_malloced);
void lmcp_init_EntityConfiguration (EntityConfiguration** i);
int lmcp_unpack_EntityConfiguration(uint8_t** buf, size_t *size_remain,EntityConfiguration* outp);
size_t lmcp_pack_EntityConfiguration(uint8_t* buf, EntityConfiguration* i);

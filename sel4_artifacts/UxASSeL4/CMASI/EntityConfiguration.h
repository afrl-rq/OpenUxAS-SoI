
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "enums.h"
#include "PayloadConfiguration.h"
#include "KeyValuePair.h"
#define LMCP_EntityConfiguration_SUB "afrl.cmasi.EntityConfiguration"

#define LMCP_EntityConfiguration_TYPENAME "EntityConfiguration"

#define LMCP_EntityConfiguration_TYPE 11

typedef struct {
    lmcp_object super;
// Units: None
    int64_t ID;

    char* Affiliation;
    array_info Affiliation_ai;

    char* EntityType;
    array_info EntityType_ai;

    char* Label;
    array_info Label_ai;

// Units: meter/sec
    float NominalSpeed;

// Units: meter
    float NominalAltitude;

    AltitudeType NominalAltitudeType;

// Units: None
    PayloadConfiguration** PayloadConfigurationList;
    array_info PayloadConfigurationList_ai;

    KeyValuePair** Info;
    array_info Info_ai;

} EntityConfiguration;
void lmcp_pp_EntityConfiguration(EntityConfiguration* s);
size_t lmcp_packsize_EntityConfiguration (EntityConfiguration* i);
size_t lmcp_pack_EntityConfiguration_header(uint8_t* buf, EntityConfiguration* i);
void lmcp_free_EntityConfiguration(EntityConfiguration* i, int out_malloced);
void lmcp_init_EntityConfiguration (EntityConfiguration** i);
int lmcp_unpack_EntityConfiguration(uint8_t** buf, size_t *size_remain,EntityConfiguration* outp);
size_t lmcp_pack_EntityConfiguration(uint8_t* buf, EntityConfiguration* i);

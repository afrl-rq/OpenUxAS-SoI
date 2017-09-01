
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "EntityConfiguration.h"
#include "FlightProfile.h"
#include "FlightProfile.h"
#include "enums.h"
#define LMCP_AirVehicleConfiguration_SUB "afrl.cmasi.AirVehicleConfiguration"

#define LMCP_AirVehicleConfiguration_TYPENAME "AirVehicleConfiguration"

#define LMCP_AirVehicleConfiguration_TYPE 13

struct AirVehicleConfiguration_struct {
    EntityConfiguration super;
// Units: meter/sec
    uint32_t minimumspeed;

// Units: meter/sec
    uint32_t maximumspeed;

    FlightProfile* nominalflightprofile;

// Units: None
    FlightProfile** alternateflightprofiles;
    array_info alternateflightprofiles_ai;

    LoiterType* availableloitertypes;
    array_info availableloitertypes_ai;

    TurnType* availableturntypes;
    array_info availableturntypes_ai;

// Units: meter
    uint32_t minimumaltitude;

    AltitudeType minaltitudetype;

// Units: meter
    uint32_t maximumaltitude;

    AltitudeType maxaltitudetype;

};
typedef struct AirVehicleConfiguration_struct AirVehicleConfiguration;
void lmcp_pp_AirVehicleConfiguration(AirVehicleConfiguration* s);
size_t lmcp_packsize_AirVehicleConfiguration (AirVehicleConfiguration* i);
size_t lmcp_pack_AirVehicleConfiguration_header(uint8_t* buf, AirVehicleConfiguration* i);
void lmcp_free_AirVehicleConfiguration(AirVehicleConfiguration* i, int out_malloced);
void lmcp_init_AirVehicleConfiguration (AirVehicleConfiguration** i);
int lmcp_unpack_AirVehicleConfiguration(uint8_t** buf, size_t *size_remain,AirVehicleConfiguration* outp);
size_t lmcp_pack_AirVehicleConfiguration(uint8_t* buf, AirVehicleConfiguration* i);

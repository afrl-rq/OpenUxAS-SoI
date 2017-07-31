
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "EntityConfiguration.h"
#include "FlightProfile.h"
#include "FlightProfile.h"
#include "enums.h"
#define LMCP_AirVehicleConfiguration_SUB "afrl.cmasi.AirVehicleConfiguration"

#define LMCP_AirVehicleConfiguration_TYPENAME "AirVehicleConfiguration"

#define LMCP_AirVehicleConfiguration_TYPE 13

typedef struct {
    EntityConfiguration super;
// Units: meter/sec
    float MinimumSpeed;

// Units: meter/sec
    float MaximumSpeed;

    FlightProfile* NominalFlightProfile;

// Units: None
    FlightProfile** AlternateFlightProfiles;
    array_info AlternateFlightProfiles_ai;

    LoiterType* AvailableLoiterTypes;
    array_info AvailableLoiterTypes_ai;

    TurnType* AvailableTurnTypes;
    array_info AvailableTurnTypes_ai;

// Units: meter
    float MinimumAltitude;

    AltitudeType MinAltitudeType;

// Units: meter
    float MaximumAltitude;

    AltitudeType MaxAltitudeType;

} AirVehicleConfiguration;
void lmcp_pp_AirVehicleConfiguration(AirVehicleConfiguration* s);
size_t lmcp_packsize_AirVehicleConfiguration (AirVehicleConfiguration* i);
size_t lmcp_pack_AirVehicleConfiguration_header(uint8_t* buf, AirVehicleConfiguration* i);
void lmcp_free_AirVehicleConfiguration(AirVehicleConfiguration* i, int out_malloced);
void lmcp_init_AirVehicleConfiguration (AirVehicleConfiguration** i);
int lmcp_unpack_AirVehicleConfiguration(uint8_t** buf, size_t *size_remain,AirVehicleConfiguration* outp);
size_t lmcp_pack_AirVehicleConfiguration(uint8_t* buf, AirVehicleConfiguration* i);

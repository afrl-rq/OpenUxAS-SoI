
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "EntityState.h"
#define LMCP_AirVehicleState_SUB "afrl.cmasi.AirVehicleState"

#define LMCP_AirVehicleState_TYPENAME "AirVehicleState"

#define LMCP_AirVehicleState_TYPE 15

typedef struct {
    EntityState super;
// Units: meter/sec
    float Airspeed;

// Units: meter/sec
    float VerticalSpeed;

// Units: meter/sec
    float WindSpeed;

// Units: degree
    float WindDirection;

} AirVehicleState;
void lmcp_pp_AirVehicleState(AirVehicleState* s);
size_t lmcp_packsize_AirVehicleState (AirVehicleState* i);
size_t lmcp_pack_AirVehicleState_header(uint8_t* buf, AirVehicleState* i);
void lmcp_free_AirVehicleState(AirVehicleState* i, int out_malloced);
void lmcp_init_AirVehicleState (AirVehicleState** i);
int lmcp_unpack_AirVehicleState(uint8_t** buf, size_t *size_remain,AirVehicleState* outp);
size_t lmcp_pack_AirVehicleState(uint8_t* buf, AirVehicleState* i);

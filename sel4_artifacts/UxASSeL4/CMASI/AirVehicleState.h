
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "EntityState.h"
#define LMCP_AirVehicleState_SUB "afrl.cmasi.AirVehicleState"

#define LMCP_AirVehicleState_TYPENAME "AirVehicleState"

#define LMCP_AirVehicleState_TYPE 15

struct AirVehicleState_struct {
    EntityState super;
// Units: meter/sec
    uint32_t airspeed;

// Units: meter/sec
    uint32_t verticalspeed;

// Units: meter/sec
    uint32_t windspeed;

// Units: degree
    uint32_t winddirection;

};
typedef struct AirVehicleState_struct AirVehicleState;
void lmcp_pp_AirVehicleState(AirVehicleState* s);
size_t lmcp_packsize_AirVehicleState (AirVehicleState* i);
size_t lmcp_pack_AirVehicleState_header(uint8_t* buf, AirVehicleState* i);
void lmcp_free_AirVehicleState(AirVehicleState* i, int out_malloced);
void lmcp_init_AirVehicleState (AirVehicleState** i);
int lmcp_unpack_AirVehicleState(uint8_t** buf, size_t *size_remain,AirVehicleState* outp);
size_t lmcp_pack_AirVehicleState(uint8_t* buf, AirVehicleState* i);

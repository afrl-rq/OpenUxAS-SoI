
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "NavigationAction.h"
#include "enums.h"
#define LMCP_FlightDirectorAction_SUB "afrl.cmasi.FlightDirectorAction"

#define LMCP_FlightDirectorAction_TYPENAME "FlightDirectorAction"

#define LMCP_FlightDirectorAction_TYPE 54

struct FlightDirectorAction_struct {
    NavigationAction super;
// Units: meter/sec
    uint32_t speed;

    SpeedType speedtype;

// Units: degree
    uint32_t heading;

// Units: meter
    uint32_t altitude;

    AltitudeType altitudetype;

// Units: meter/sec
    uint32_t climbrate;

};
typedef struct FlightDirectorAction_struct FlightDirectorAction;
void lmcp_pp_FlightDirectorAction(FlightDirectorAction* s);
size_t lmcp_packsize_FlightDirectorAction (FlightDirectorAction* i);
size_t lmcp_pack_FlightDirectorAction_header(uint8_t* buf, FlightDirectorAction* i);
void lmcp_free_FlightDirectorAction(FlightDirectorAction* i, int out_malloced);
void lmcp_init_FlightDirectorAction (FlightDirectorAction** i);
int lmcp_unpack_FlightDirectorAction(uint8_t** buf, size_t *size_remain,FlightDirectorAction* outp);
size_t lmcp_pack_FlightDirectorAction(uint8_t* buf, FlightDirectorAction* i);

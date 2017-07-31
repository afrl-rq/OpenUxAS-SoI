
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "enums.h"
#include "AbstractGeometry.h"
#define LMCP_AbstractZone_SUB "afrl.cmasi.AbstractZone"

#define LMCP_AbstractZone_TYPENAME "AbstractZone"

#define LMCP_AbstractZone_TYPE 10

typedef struct {
    lmcp_object super;
// Units: None
    int64_t ZoneID;

// Units: meter
    float MinAltitude;

    AltitudeType MinAltitudeType;

// Units: meter
    float MaxAltitude;

    AltitudeType MaxAltitudeType;

// Units: None
    int64_t* AffectedAircraft;
    array_info AffectedAircraft_ai;

// Units: milliseconds
    int64_t StartTime;

// Units: milliseconds
    int64_t EndTime;

// Units: meters
    float Padding;

    char* Label;
    array_info Label_ai;

// Units: None
    AbstractGeometry* Boundary;

} AbstractZone;
void lmcp_pp_AbstractZone(AbstractZone* s);
size_t lmcp_packsize_AbstractZone (AbstractZone* i);
size_t lmcp_pack_AbstractZone_header(uint8_t* buf, AbstractZone* i);
void lmcp_free_AbstractZone(AbstractZone* i, int out_malloced);
void lmcp_init_AbstractZone (AbstractZone** i);
int lmcp_unpack_AbstractZone(uint8_t** buf, size_t *size_remain,AbstractZone* outp);
size_t lmcp_pack_AbstractZone(uint8_t* buf, AbstractZone* i);

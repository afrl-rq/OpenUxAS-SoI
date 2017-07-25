
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "enums.h"
#define LMCP_Location3D_SUB "afrl.cmasi.Location3D"

#define LMCP_Location3D_TYPENAME "Location3D"

#define LMCP_Location3D_TYPE 3

typedef struct {
    lmcp_object super;
// Units: degree
    double Latitude;

// Units: degree
    double Longitude;

// Units: meter
    float Altitude;

    AltitudeType AltitudeType;

} Location3D;
void lmcp_pp_Location3D(Location3D* s);
size_t lmcp_packsize_Location3D (Location3D* i);
size_t lmcp_pack_Location3D_header(uint8_t* buf, Location3D* i);
void lmcp_free_Location3D(Location3D* i, int out_malloced);
void lmcp_init_Location3D (Location3D** i);
int lmcp_unpack_Location3D(uint8_t** buf, size_t *size_remain,Location3D* outp);
size_t lmcp_pack_Location3D(uint8_t* buf, Location3D* i);

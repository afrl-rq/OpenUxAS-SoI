
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "enums.h"
#define LMCP_Location3D_SUB "afrl.cmasi.Location3D"

#define LMCP_Location3D_TYPENAME "Location3D"

#define LMCP_Location3D_TYPE 3

struct Location3D_struct {
    lmcp_object super;
// Units: degree
    uint64_t latitude;

// Units: degree
    uint64_t longitude;

// Units: meter
    uint32_t altitude;

    AltitudeType altitudetype;

};
typedef struct Location3D_struct Location3D;
void lmcp_pp_Location3D(Location3D* s);
size_t lmcp_packsize_Location3D (Location3D* i);
size_t lmcp_pack_Location3D_header(uint8_t* buf, Location3D* i);
void lmcp_free_Location3D(Location3D* i, int out_malloced);
void lmcp_init_Location3D (Location3D** i);
int lmcp_unpack_Location3D(uint8_t** buf, size_t *size_remain,Location3D* outp);
size_t lmcp_pack_Location3D(uint8_t* buf, Location3D* i);


#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AbstractGeometry.h"
#include "Location3D.h"
#define LMCP_Rectangle_SUB "afrl.cmasi.Rectangle"

#define LMCP_Rectangle_TYPENAME "Rectangle"

#define LMCP_Rectangle_TYPE 43

typedef struct {
    AbstractGeometry super;
    Location3D* CenterPoint;

// Units: meter
    float Width;

// Units: meter
    float Height;

// Units: degree
    float Rotation;

} Rectangle;
void lmcp_pp_Rectangle(Rectangle* s);
size_t lmcp_packsize_Rectangle (Rectangle* i);
size_t lmcp_pack_Rectangle_header(uint8_t* buf, Rectangle* i);
void lmcp_free_Rectangle(Rectangle* i, int out_malloced);
void lmcp_init_Rectangle (Rectangle** i);
int lmcp_unpack_Rectangle(uint8_t** buf, size_t *size_remain,Rectangle* outp);
size_t lmcp_pack_Rectangle(uint8_t* buf, Rectangle* i);

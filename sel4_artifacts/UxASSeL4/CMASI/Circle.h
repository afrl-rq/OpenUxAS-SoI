
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AbstractGeometry.h"
#include "Location3D.h"
#define LMCP_Circle_SUB "afrl.cmasi.Circle"

#define LMCP_Circle_TYPENAME "Circle"

#define LMCP_Circle_TYPE 22

typedef struct {
    AbstractGeometry super;
    Location3D* CenterPoint;

// Units: meter
    float Radius;

} Circle;
void lmcp_pp_Circle(Circle* s);
size_t lmcp_packsize_Circle (Circle* i);
size_t lmcp_pack_Circle_header(uint8_t* buf, Circle* i);
void lmcp_free_Circle(Circle* i, int out_malloced);
void lmcp_init_Circle (Circle** i);
int lmcp_unpack_Circle(uint8_t** buf, size_t *size_remain,Circle* outp);
size_t lmcp_pack_Circle(uint8_t* buf, Circle* i);


#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_Wedge_SUB "afrl.cmasi.Wedge"

#define LMCP_Wedge_TYPENAME "Wedge"

#define LMCP_Wedge_TYPE 16

struct Wedge_struct {
    lmcp_object super;
// Units: degree
    uint32_t azimuthcenterline;

// Units: degree
    uint32_t verticalcenterline;

// Units: degree
    uint32_t azimuthextent;

// Units: degree
    uint32_t verticalextent;

};
typedef struct Wedge_struct Wedge;
void lmcp_pp_Wedge(Wedge* s);
size_t lmcp_packsize_Wedge (Wedge* i);
size_t lmcp_pack_Wedge_header(uint8_t* buf, Wedge* i);
void lmcp_free_Wedge(Wedge* i, int out_malloced);
void lmcp_init_Wedge (Wedge** i);
int lmcp_unpack_Wedge(uint8_t** buf, size_t *size_remain,Wedge* outp);
size_t lmcp_pack_Wedge(uint8_t* buf, Wedge* i);

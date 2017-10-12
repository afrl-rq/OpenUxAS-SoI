
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_OperatingRegion_SUB "afrl.cmasi.OperatingRegion"

#define LMCP_OperatingRegion_TYPENAME "OperatingRegion"

#define LMCP_OperatingRegion_TYPE 39

struct OperatingRegion_struct {
    lmcp_object super;
    int64_t id;

    int64_t* keepinareas;
    array_info keepinareas_ai;

    int64_t* keepoutareas;
    array_info keepoutareas_ai;

};
typedef struct OperatingRegion_struct OperatingRegion;
void lmcp_pp_OperatingRegion(OperatingRegion* s);
size_t lmcp_packsize_OperatingRegion (OperatingRegion* i);
size_t lmcp_pack_OperatingRegion_header(uint8_t* buf, OperatingRegion* i);
void lmcp_free_OperatingRegion(OperatingRegion* i, int out_malloced);
void lmcp_init_OperatingRegion (OperatingRegion** i);
int lmcp_unpack_OperatingRegion(uint8_t** buf, size_t *size_remain,OperatingRegion* outp);
size_t lmcp_pack_OperatingRegion(uint8_t* buf, OperatingRegion* i);

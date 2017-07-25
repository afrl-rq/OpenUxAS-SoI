
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_OperatingRegion_SUB "afrl.cmasi.OperatingRegion"

#define LMCP_OperatingRegion_TYPENAME "OperatingRegion"

#define LMCP_OperatingRegion_TYPE 39

typedef struct {
    lmcp_object super;
    int64_t ID;

    int64_t* KeepInAreas;
    array_info KeepInAreas_ai;

    int64_t* KeepOutAreas;
    array_info KeepOutAreas_ai;

} OperatingRegion;
void lmcp_pp_OperatingRegion(OperatingRegion* s);
size_t lmcp_packsize_OperatingRegion (OperatingRegion* i);
size_t lmcp_pack_OperatingRegion_header(uint8_t* buf, OperatingRegion* i);
void lmcp_free_OperatingRegion(OperatingRegion* i, int out_malloced);
void lmcp_init_OperatingRegion (OperatingRegion** i);
int lmcp_unpack_OperatingRegion(uint8_t** buf, size_t *size_remain,OperatingRegion* outp);
size_t lmcp_pack_OperatingRegion(uint8_t* buf, OperatingRegion* i);

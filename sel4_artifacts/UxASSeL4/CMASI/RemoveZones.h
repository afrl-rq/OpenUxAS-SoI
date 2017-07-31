
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_RemoveZones_SUB "afrl.cmasi.RemoveZones"

#define LMCP_RemoveZones_TYPENAME "RemoveZones"

#define LMCP_RemoveZones_TYPE 52

typedef struct {
    lmcp_object super;
    int64_t* ZoneList;
    array_info ZoneList_ai;

} RemoveZones;
void lmcp_pp_RemoveZones(RemoveZones* s);
size_t lmcp_packsize_RemoveZones (RemoveZones* i);
size_t lmcp_pack_RemoveZones_header(uint8_t* buf, RemoveZones* i);
void lmcp_free_RemoveZones(RemoveZones* i, int out_malloced);
void lmcp_init_RemoveZones (RemoveZones** i);
int lmcp_unpack_RemoveZones(uint8_t** buf, size_t *size_remain,RemoveZones* outp);
size_t lmcp_pack_RemoveZones(uint8_t* buf, RemoveZones* i);

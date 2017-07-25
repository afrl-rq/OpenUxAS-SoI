
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_RemoveEntities_SUB "afrl.cmasi.RemoveEntities"

#define LMCP_RemoveEntities_TYPENAME "RemoveEntities"

#define LMCP_RemoveEntities_TYPE 53

typedef struct {
    lmcp_object super;
    int64_t* EntityList;
    array_info EntityList_ai;

} RemoveEntities;
void lmcp_pp_RemoveEntities(RemoveEntities* s);
size_t lmcp_packsize_RemoveEntities (RemoveEntities* i);
size_t lmcp_pack_RemoveEntities_header(uint8_t* buf, RemoveEntities* i);
void lmcp_free_RemoveEntities(RemoveEntities* i, int out_malloced);
void lmcp_init_RemoveEntities (RemoveEntities** i);
int lmcp_unpack_RemoveEntities(uint8_t** buf, size_t *size_remain,RemoveEntities* outp);
size_t lmcp_pack_RemoveEntities(uint8_t* buf, RemoveEntities* i);

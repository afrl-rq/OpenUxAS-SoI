
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AbstractZone.h"
#include "enums.h"
#define LMCP_KeepOutZone_SUB "afrl.cmasi.KeepOutZone"

#define LMCP_KeepOutZone_TYPENAME "KeepOutZone"

#define LMCP_KeepOutZone_TYPE 30

typedef struct {
    AbstractZone super;
// Units: None
    ZoneAvoidanceType ZoneType;

} KeepOutZone;
void lmcp_pp_KeepOutZone(KeepOutZone* s);
size_t lmcp_packsize_KeepOutZone (KeepOutZone* i);
size_t lmcp_pack_KeepOutZone_header(uint8_t* buf, KeepOutZone* i);
void lmcp_free_KeepOutZone(KeepOutZone* i, int out_malloced);
void lmcp_init_KeepOutZone (KeepOutZone** i);
int lmcp_unpack_KeepOutZone(uint8_t** buf, size_t *size_remain,KeepOutZone* outp);
size_t lmcp_pack_KeepOutZone(uint8_t* buf, KeepOutZone* i);

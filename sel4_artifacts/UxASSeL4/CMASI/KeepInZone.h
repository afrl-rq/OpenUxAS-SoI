
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AbstractZone.h"
#define LMCP_KeepInZone_SUB "afrl.cmasi.KeepInZone"

#define LMCP_KeepInZone_TYPENAME "KeepInZone"

#define LMCP_KeepInZone_TYPE 29

typedef struct {
    AbstractZone super;
} KeepInZone;
void lmcp_pp_KeepInZone(KeepInZone* s);
size_t lmcp_packsize_KeepInZone (KeepInZone* i);
size_t lmcp_pack_KeepInZone_header(uint8_t* buf, KeepInZone* i);
void lmcp_free_KeepInZone(KeepInZone* i, int out_malloced);
void lmcp_init_KeepInZone (KeepInZone** i);
int lmcp_unpack_KeepInZone(uint8_t** buf, size_t *size_remain,KeepInZone* outp);
size_t lmcp_pack_KeepInZone(uint8_t* buf, KeepInZone* i);

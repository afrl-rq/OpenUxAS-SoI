
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_KeyValuePair_SUB "afrl.cmasi.KeyValuePair"

#define LMCP_KeyValuePair_TYPENAME "KeyValuePair"

#define LMCP_KeyValuePair_TYPE 2

typedef struct {
    lmcp_object super;
    char* Key;
    array_info Key_ai;

    char* Value;
    array_info Value_ai;

} KeyValuePair;
void lmcp_pp_KeyValuePair(KeyValuePair* s);
size_t lmcp_packsize_KeyValuePair (KeyValuePair* i);
size_t lmcp_pack_KeyValuePair_header(uint8_t* buf, KeyValuePair* i);
void lmcp_free_KeyValuePair(KeyValuePair* i, int out_malloced);
void lmcp_init_KeyValuePair (KeyValuePair** i);
int lmcp_unpack_KeyValuePair(uint8_t** buf, size_t *size_remain,KeyValuePair* outp);
size_t lmcp_pack_KeyValuePair(uint8_t* buf, KeyValuePair* i);

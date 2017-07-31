
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "KeyValuePair.h"
#define LMCP_PayloadState_SUB "afrl.cmasi.PayloadState"

#define LMCP_PayloadState_TYPENAME "PayloadState"

#define LMCP_PayloadState_TYPE 6

typedef struct {
    lmcp_object super;
// Units: None
    int64_t PayloadID;

    KeyValuePair** Parameters;
    array_info Parameters_ai;

} PayloadState;
void lmcp_pp_PayloadState(PayloadState* s);
size_t lmcp_packsize_PayloadState (PayloadState* i);
size_t lmcp_pack_PayloadState_header(uint8_t* buf, PayloadState* i);
void lmcp_free_PayloadState(PayloadState* i, int out_malloced);
void lmcp_init_PayloadState (PayloadState** i);
int lmcp_unpack_PayloadState(uint8_t** buf, size_t *size_remain,PayloadState* outp);
size_t lmcp_pack_PayloadState(uint8_t* buf, PayloadState* i);

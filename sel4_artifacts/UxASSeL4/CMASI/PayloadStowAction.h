
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_PayloadStowAction_SUB "afrl.cmasi.PayloadStowAction"

#define LMCP_PayloadStowAction_TYPENAME "PayloadStowAction"

#define LMCP_PayloadStowAction_TYPE 60

typedef struct {
    lmcp_object super;
    int64_t PayloadID;

} PayloadStowAction;
void lmcp_pp_PayloadStowAction(PayloadStowAction* s);
size_t lmcp_packsize_PayloadStowAction (PayloadStowAction* i);
size_t lmcp_pack_PayloadStowAction_header(uint8_t* buf, PayloadStowAction* i);
void lmcp_free_PayloadStowAction(PayloadStowAction* i, int out_malloced);
void lmcp_init_PayloadStowAction (PayloadStowAction** i);
int lmcp_unpack_PayloadStowAction(uint8_t** buf, size_t *size_remain,PayloadStowAction* outp);
size_t lmcp_pack_PayloadStowAction(uint8_t* buf, PayloadStowAction* i);

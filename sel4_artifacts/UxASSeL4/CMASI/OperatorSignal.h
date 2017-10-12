
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "KeyValuePair.h"
#define LMCP_OperatorSignal_SUB "afrl.cmasi.OperatorSignal"

#define LMCP_OperatorSignal_TYPENAME "OperatorSignal"

#define LMCP_OperatorSignal_TYPE 38

struct OperatorSignal_struct {
    lmcp_object super;
    KeyValuePair** signals;
    array_info signals_ai;

};
typedef struct OperatorSignal_struct OperatorSignal;
void lmcp_pp_OperatorSignal(OperatorSignal* s);
size_t lmcp_packsize_OperatorSignal (OperatorSignal* i);
size_t lmcp_pack_OperatorSignal_header(uint8_t* buf, OperatorSignal* i);
void lmcp_free_OperatorSignal(OperatorSignal* i, int out_malloced);
void lmcp_init_OperatorSignal (OperatorSignal** i);
int lmcp_unpack_OperatorSignal(uint8_t** buf, size_t *size_remain,OperatorSignal* outp);
size_t lmcp_pack_OperatorSignal(uint8_t* buf, OperatorSignal* i);

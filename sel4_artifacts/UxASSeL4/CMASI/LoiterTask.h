
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Task.h"
#include "LoiterAction.h"
#define LMCP_LoiterTask_SUB "afrl.cmasi.LoiterTask"

#define LMCP_LoiterTask_TYPENAME "LoiterTask"

#define LMCP_LoiterTask_TYPE 34

typedef struct {
    Task super;
// Units: none
    LoiterAction* DesiredAction;

} LoiterTask;
void lmcp_pp_LoiterTask(LoiterTask* s);
size_t lmcp_packsize_LoiterTask (LoiterTask* i);
size_t lmcp_pack_LoiterTask_header(uint8_t* buf, LoiterTask* i);
void lmcp_free_LoiterTask(LoiterTask* i, int out_malloced);
void lmcp_init_LoiterTask (LoiterTask** i);
int lmcp_unpack_LoiterTask(uint8_t** buf, size_t *size_remain,LoiterTask* outp);
size_t lmcp_pack_LoiterTask(uint8_t* buf, LoiterTask* i);

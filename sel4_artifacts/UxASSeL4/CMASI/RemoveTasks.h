
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_RemoveTasks_SUB "afrl.cmasi.RemoveTasks"

#define LMCP_RemoveTasks_TYPENAME "RemoveTasks"

#define LMCP_RemoveTasks_TYPE 44

typedef struct {
    lmcp_object super;
    int64_t* TaskList;
    array_info TaskList_ai;

} RemoveTasks;
void lmcp_pp_RemoveTasks(RemoveTasks* s);
size_t lmcp_packsize_RemoveTasks (RemoveTasks* i);
size_t lmcp_pack_RemoveTasks_header(uint8_t* buf, RemoveTasks* i);
void lmcp_free_RemoveTasks(RemoveTasks* i, int out_malloced);
void lmcp_init_RemoveTasks (RemoveTasks** i);
int lmcp_unpack_RemoveTasks(uint8_t** buf, size_t *size_remain,RemoveTasks* outp);
size_t lmcp_pack_RemoveTasks(uint8_t* buf, RemoveTasks* i);


#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_AutomationRequest_SUB "afrl.cmasi.AutomationRequest"

#define LMCP_AutomationRequest_TYPENAME "AutomationRequest"

#define LMCP_AutomationRequest_TYPE 40

typedef struct {
    lmcp_object super;
    int64_t* EntityList;
    array_info EntityList_ai;

    int64_t* TaskList;
    array_info TaskList_ai;

    char* TaskRelationships;
    array_info TaskRelationships_ai;

    int64_t OperatingRegion;

    uint8_t RedoAllTasks;

} AutomationRequest;
void lmcp_pp_AutomationRequest(AutomationRequest* s);
size_t lmcp_packsize_AutomationRequest (AutomationRequest* i);
size_t lmcp_pack_AutomationRequest_header(uint8_t* buf, AutomationRequest* i);
void lmcp_free_AutomationRequest(AutomationRequest* i, int out_malloced);
void lmcp_init_AutomationRequest (AutomationRequest** i);
int lmcp_unpack_AutomationRequest(uint8_t** buf, size_t *size_remain,AutomationRequest* outp);
size_t lmcp_pack_AutomationRequest(uint8_t* buf, AutomationRequest* i);

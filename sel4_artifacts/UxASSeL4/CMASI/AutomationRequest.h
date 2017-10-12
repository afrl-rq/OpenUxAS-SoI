
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_AutomationRequest_SUB "afrl.cmasi.AutomationRequest"

#define LMCP_AutomationRequest_TYPENAME "AutomationRequest"

#define LMCP_AutomationRequest_TYPE 40

struct AutomationRequest_struct {
    lmcp_object super;
    int64_t* entitylist;
    array_info entitylist_ai;

    int64_t* tasklist;
    array_info tasklist_ai;

    char* taskrelationships;
    array_info taskrelationships_ai;

    int64_t operatingregion;

    uint8_t redoalltasks;

};
typedef struct AutomationRequest_struct AutomationRequest;
void lmcp_pp_AutomationRequest(AutomationRequest* s);
size_t lmcp_packsize_AutomationRequest (AutomationRequest* i);
size_t lmcp_pack_AutomationRequest_header(uint8_t* buf, AutomationRequest* i);
void lmcp_free_AutomationRequest(AutomationRequest* i, int out_malloced);
void lmcp_init_AutomationRequest (AutomationRequest** i);
int lmcp_unpack_AutomationRequest(uint8_t** buf, size_t *size_remain,AutomationRequest* outp);
size_t lmcp_pack_AutomationRequest(uint8_t* buf, AutomationRequest* i);

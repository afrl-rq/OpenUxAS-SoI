
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "MissionCommand.h"
#include "VehicleActionCommand.h"
#include "KeyValuePair.h"
#define LMCP_AutomationResponse_SUB "afrl.cmasi.AutomationResponse"

#define LMCP_AutomationResponse_TYPENAME "AutomationResponse"

#define LMCP_AutomationResponse_TYPE 51

typedef struct {
    lmcp_object super;
    MissionCommand** MissionCommandList;
    array_info MissionCommandList_ai;

    VehicleActionCommand** VehicleCommandList;
    array_info VehicleCommandList_ai;

    KeyValuePair** Info;
    array_info Info_ai;

} AutomationResponse;
void lmcp_pp_AutomationResponse(AutomationResponse* s);
size_t lmcp_packsize_AutomationResponse (AutomationResponse* i);
size_t lmcp_pack_AutomationResponse_header(uint8_t* buf, AutomationResponse* i);
void lmcp_free_AutomationResponse(AutomationResponse* i, int out_malloced);
void lmcp_init_AutomationResponse (AutomationResponse** i);
int lmcp_unpack_AutomationResponse(uint8_t** buf, size_t *size_remain,AutomationResponse* outp);
size_t lmcp_pack_AutomationResponse(uint8_t* buf, AutomationResponse* i);


#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "KeyValuePair.h"
#include "enums.h"
#define LMCP_ServiceStatus_SUB "afrl.cmasi.ServiceStatus"

#define LMCP_ServiceStatus_TYPENAME "ServiceStatus"

#define LMCP_ServiceStatus_TYPE 45

typedef struct {
    lmcp_object super;
    float PercentComplete;

    KeyValuePair** Info;
    array_info Info_ai;

    ServiceStatusType StatusType;

} ServiceStatus;
void lmcp_pp_ServiceStatus(ServiceStatus* s);
size_t lmcp_packsize_ServiceStatus (ServiceStatus* i);
size_t lmcp_pack_ServiceStatus_header(uint8_t* buf, ServiceStatus* i);
void lmcp_free_ServiceStatus(ServiceStatus* i, int out_malloced);
void lmcp_init_ServiceStatus (ServiceStatus** i);
int lmcp_unpack_ServiceStatus(uint8_t** buf, size_t *size_remain,ServiceStatus* outp);
size_t lmcp_pack_ServiceStatus(uint8_t* buf, ServiceStatus* i);

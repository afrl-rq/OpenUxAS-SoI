
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "KeyValuePair.h"
#define LMCP_PayloadConfiguration_SUB "afrl.cmasi.PayloadConfiguration"

#define LMCP_PayloadConfiguration_TYPENAME "PayloadConfiguration"

#define LMCP_PayloadConfiguration_TYPE 5

struct PayloadConfiguration_struct {
    lmcp_object super;
// Units: None
    int64_t payloadid;

// Units: None
    char* payloadkind;
    array_info payloadkind_ai;

    KeyValuePair** parameters;
    array_info parameters_ai;

};
typedef struct PayloadConfiguration_struct PayloadConfiguration;
void lmcp_pp_PayloadConfiguration(PayloadConfiguration* s);
size_t lmcp_packsize_PayloadConfiguration (PayloadConfiguration* i);
size_t lmcp_pack_PayloadConfiguration_header(uint8_t* buf, PayloadConfiguration* i);
void lmcp_free_PayloadConfiguration(PayloadConfiguration* i, int out_malloced);
void lmcp_init_PayloadConfiguration (PayloadConfiguration** i);
int lmcp_unpack_PayloadConfiguration(uint8_t** buf, size_t *size_remain,PayloadConfiguration* outp);
size_t lmcp_pack_PayloadConfiguration(uint8_t* buf, PayloadConfiguration* i);

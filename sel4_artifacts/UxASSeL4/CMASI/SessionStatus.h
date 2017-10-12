
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "enums.h"
#include "KeyValuePair.h"
#define LMCP_SessionStatus_SUB "afrl.cmasi.SessionStatus"

#define LMCP_SessionStatus_TYPENAME "SessionStatus"

#define LMCP_SessionStatus_TYPE 46

struct SessionStatus_struct {
    lmcp_object super;
    SimulationStatusType state;

// Units: millisecond
    int64_t starttime;

// Units: millisecond
    int64_t scenariotime;

    uint32_t realtimemultiple;

    KeyValuePair** parameters;
    array_info parameters_ai;

};
typedef struct SessionStatus_struct SessionStatus;
void lmcp_pp_SessionStatus(SessionStatus* s);
size_t lmcp_packsize_SessionStatus (SessionStatus* i);
size_t lmcp_pack_SessionStatus_header(uint8_t* buf, SessionStatus* i);
void lmcp_free_SessionStatus(SessionStatus* i, int out_malloced);
void lmcp_init_SessionStatus (SessionStatus** i);
int lmcp_unpack_SessionStatus(uint8_t** buf, size_t *size_remain,SessionStatus* outp);
size_t lmcp_pack_SessionStatus(uint8_t* buf, SessionStatus* i);

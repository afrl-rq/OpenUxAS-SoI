
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "enums.h"
#include "KeyValuePair.h"
#define LMCP_SessionStatus_SUB "afrl.cmasi.SessionStatus"

#define LMCP_SessionStatus_TYPENAME "SessionStatus"

#define LMCP_SessionStatus_TYPE 46

typedef struct {
    lmcp_object super;
    SimulationStatusType State;

// Units: millisecond
    int64_t StartTime;

// Units: millisecond
    int64_t ScenarioTime;

    float RealTimeMultiple;

    KeyValuePair** Parameters;
    array_info Parameters_ai;

} SessionStatus;
void lmcp_pp_SessionStatus(SessionStatus* s);
size_t lmcp_packsize_SessionStatus (SessionStatus* i);
size_t lmcp_pack_SessionStatus_header(uint8_t* buf, SessionStatus* i);
void lmcp_free_SessionStatus(SessionStatus* i, int out_malloced);
void lmcp_init_SessionStatus (SessionStatus** i);
int lmcp_unpack_SessionStatus(uint8_t** buf, size_t *size_remain,SessionStatus* outp);
size_t lmcp_pack_SessionStatus(uint8_t* buf, SessionStatus* i);

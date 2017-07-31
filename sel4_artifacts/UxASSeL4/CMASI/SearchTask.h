
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Task.h"
#include "enums.h"
#define LMCP_SearchTask_SUB "afrl.cmasi.SearchTask"

#define LMCP_SearchTask_TYPENAME "SearchTask"

#define LMCP_SearchTask_TYPE 9

typedef struct {
    Task super;
    WavelengthBand* DesiredWavelengthBands;
    array_info DesiredWavelengthBands_ai;

// Units: milliseconds
    int64_t DwellTime;

// Units: meters/pixel
    float GroundSampleDistance;

} SearchTask;
void lmcp_pp_SearchTask(SearchTask* s);
size_t lmcp_packsize_SearchTask (SearchTask* i);
size_t lmcp_pack_SearchTask_header(uint8_t* buf, SearchTask* i);
void lmcp_free_SearchTask(SearchTask* i, int out_malloced);
void lmcp_init_SearchTask (SearchTask** i);
int lmcp_unpack_SearchTask(uint8_t** buf, size_t *size_remain,SearchTask* outp);
size_t lmcp_pack_SearchTask(uint8_t* buf, SearchTask* i);

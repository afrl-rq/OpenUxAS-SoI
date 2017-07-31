
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "SearchTask.h"
#include "Location3D.h"
#include "Wedge.h"
#define LMCP_PointSearchTask_SUB "afrl.cmasi.PointSearchTask"

#define LMCP_PointSearchTask_TYPENAME "PointSearchTask"

#define LMCP_PointSearchTask_TYPE 41

typedef struct {
    SearchTask super;
    Location3D* SearchLocation;

// Units: meter
    float StandoffDistance;

    Wedge** ViewAngleList;
    array_info ViewAngleList_ai;

} PointSearchTask;
void lmcp_pp_PointSearchTask(PointSearchTask* s);
size_t lmcp_packsize_PointSearchTask (PointSearchTask* i);
size_t lmcp_pack_PointSearchTask_header(uint8_t* buf, PointSearchTask* i);
void lmcp_free_PointSearchTask(PointSearchTask* i, int out_malloced);
void lmcp_init_PointSearchTask (PointSearchTask** i);
int lmcp_unpack_PointSearchTask(uint8_t** buf, size_t *size_remain,PointSearchTask* outp);
size_t lmcp_pack_PointSearchTask(uint8_t* buf, PointSearchTask* i);

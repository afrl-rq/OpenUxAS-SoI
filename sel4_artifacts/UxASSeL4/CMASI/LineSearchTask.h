
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "SearchTask.h"
#include "Location3D.h"
#include "Wedge.h"
#define LMCP_LineSearchTask_SUB "afrl.cmasi.LineSearchTask"

#define LMCP_LineSearchTask_TYPENAME "LineSearchTask"

#define LMCP_LineSearchTask_TYPE 31

typedef struct {
    SearchTask super;
    Location3D** PointList;
    array_info PointList_ai;

    Wedge** ViewAngleList;
    array_info ViewAngleList_ai;

    uint8_t UseInertialViewAngles;

} LineSearchTask;
void lmcp_pp_LineSearchTask(LineSearchTask* s);
size_t lmcp_packsize_LineSearchTask (LineSearchTask* i);
size_t lmcp_pack_LineSearchTask_header(uint8_t* buf, LineSearchTask* i);
void lmcp_free_LineSearchTask(LineSearchTask* i, int out_malloced);
void lmcp_init_LineSearchTask (LineSearchTask** i);
int lmcp_unpack_LineSearchTask(uint8_t** buf, size_t *size_remain,LineSearchTask* outp);
size_t lmcp_pack_LineSearchTask(uint8_t* buf, LineSearchTask* i);

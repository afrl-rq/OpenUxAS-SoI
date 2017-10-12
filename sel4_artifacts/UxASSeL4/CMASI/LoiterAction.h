
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "NavigationAction.h"
#include "enums.h"
#include "Location3D.h"
#define LMCP_LoiterAction_SUB "afrl.cmasi.LoiterAction"

#define LMCP_LoiterAction_TYPENAME "LoiterAction"

#define LMCP_LoiterAction_TYPE 33

struct LoiterAction_struct {
    NavigationAction super;
// Units: none
    LoiterType loitertype;

// Units: meter
    uint32_t radius;

// Units: degree
    uint32_t axis;

// Units: meter
    uint32_t length;

// Units: None
    LoiterDirection direction;

// Units: milliseconds
    int64_t duration;

// Units: meter/sec
    uint32_t airspeed;

    Location3D* location;

};
typedef struct LoiterAction_struct LoiterAction;
void lmcp_pp_LoiterAction(LoiterAction* s);
size_t lmcp_packsize_LoiterAction (LoiterAction* i);
size_t lmcp_pack_LoiterAction_header(uint8_t* buf, LoiterAction* i);
void lmcp_free_LoiterAction(LoiterAction* i, int out_malloced);
void lmcp_init_LoiterAction (LoiterAction** i);
int lmcp_unpack_LoiterAction(uint8_t** buf, size_t *size_remain,LoiterAction* outp);
size_t lmcp_pack_LoiterAction(uint8_t* buf, LoiterAction* i);


#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadAction.h"
#include "PayloadAction.h"
#define LMCP_CameraAction_SUB "afrl.cmasi.CameraAction"

#define LMCP_CameraAction_TYPENAME "CameraAction"

#define LMCP_CameraAction_TYPE 18

struct CameraAction_struct {
    PayloadAction super;
// Units: degree
    uint32_t horizontalfieldofview;

    PayloadAction** associatedactions;
    array_info associatedactions_ai;

};
typedef struct CameraAction_struct CameraAction;
void lmcp_pp_CameraAction(CameraAction* s);
size_t lmcp_packsize_CameraAction (CameraAction* i);
size_t lmcp_pack_CameraAction_header(uint8_t* buf, CameraAction* i);
void lmcp_free_CameraAction(CameraAction* i, int out_malloced);
void lmcp_init_CameraAction (CameraAction** i);
int lmcp_unpack_CameraAction(uint8_t** buf, size_t *size_remain,CameraAction* outp);
size_t lmcp_pack_CameraAction(uint8_t* buf, CameraAction* i);

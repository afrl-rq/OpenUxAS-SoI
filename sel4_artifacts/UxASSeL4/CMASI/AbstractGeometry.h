
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#define LMCP_AbstractGeometry_SUB "afrl.cmasi.AbstractGeometry"

#define LMCP_AbstractGeometry_TYPENAME "AbstractGeometry"

#define LMCP_AbstractGeometry_TYPE 1

typedef struct {
    lmcp_object super;
} AbstractGeometry;
void lmcp_pp_AbstractGeometry(AbstractGeometry* s);
size_t lmcp_packsize_AbstractGeometry (AbstractGeometry* i);
size_t lmcp_pack_AbstractGeometry_header(uint8_t* buf, AbstractGeometry* i);
void lmcp_free_AbstractGeometry(AbstractGeometry* i, int out_malloced);
void lmcp_init_AbstractGeometry (AbstractGeometry** i);
int lmcp_unpack_AbstractGeometry(uint8_t** buf, size_t *size_remain,AbstractGeometry* outp);
size_t lmcp_pack_AbstractGeometry(uint8_t* buf, AbstractGeometry* i);

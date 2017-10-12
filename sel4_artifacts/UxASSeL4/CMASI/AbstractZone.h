
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "enums.h"
#include "AbstractGeometry.h"
#define LMCP_AbstractZone_SUB "afrl.cmasi.AbstractZone"

#define LMCP_AbstractZone_TYPENAME "AbstractZone"

#define LMCP_AbstractZone_TYPE 10

struct AbstractZone_struct {
    lmcp_object super;
// Units: None
    int64_t zoneid;

// Units: meter
    uint32_t minaltitude;

    AltitudeType minaltitudetype;

// Units: meter
    uint32_t maxaltitude;

    AltitudeType maxaltitudetype;

// Units: None
    int64_t* affectedaircraft;
    array_info affectedaircraft_ai;

// Units: milliseconds
    int64_t starttime;

// Units: milliseconds
    int64_t endtime;

// Units: meters
    uint32_t padding;

    char* label;
    array_info label_ai;

// Units: None
    AbstractGeometry* boundary;

};
typedef struct AbstractZone_struct AbstractZone;
void lmcp_pp_AbstractZone(AbstractZone* s);
size_t lmcp_packsize_AbstractZone (AbstractZone* i);
size_t lmcp_pack_AbstractZone_header(uint8_t* buf, AbstractZone* i);
void lmcp_free_AbstractZone(AbstractZone* i, int out_malloced);
void lmcp_init_AbstractZone (AbstractZone** i);
int lmcp_unpack_AbstractZone(uint8_t** buf, size_t *size_remain,AbstractZone* outp);
size_t lmcp_pack_AbstractZone(uint8_t* buf, AbstractZone* i);

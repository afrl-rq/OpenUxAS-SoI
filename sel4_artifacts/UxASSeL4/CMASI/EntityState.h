
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Location3D.h"
#include "PayloadState.h"
#include "enums.h"
#include "KeyValuePair.h"
#define LMCP_EntityState_SUB "afrl.cmasi.EntityState"

#define LMCP_EntityState_TYPENAME "EntityState"

#define LMCP_EntityState_TYPE 14

struct EntityState_struct {
    lmcp_object super;
    int64_t id;

// Units: meter/sec
    uint32_t u;

// Units: meter/sec
    uint32_t v;

// Units: meter/sec
    uint32_t w;

// Units: meter/sec/sec
    uint32_t udot;

// Units: meter/sec/sec
    uint32_t vdot;

// Units: meter/sec/sec
    uint32_t wdot;

// Units: degree
    uint32_t heading;

// Units: degree
    uint32_t pitch;

// Units: degree
    uint32_t roll;

// Units: degree/sec
    uint32_t p;

// Units: degree/sec
    uint32_t q;

// Units: degree/sec
    uint32_t r;

// Units: degrees
    uint32_t course;

// Units: m/s
    uint32_t groundspeed;

    Location3D* location;

// Units: %
    uint32_t energyavailable;

// Units: %/sec
    uint32_t actualenergyrate;

    PayloadState** payloadstatelist;
    array_info payloadstatelist_ai;

// Units: None
    int64_t currentwaypoint;

    int64_t currentcommand;

// Units: None
    NavigationMode mode;

// Units: None
    int64_t* associatedtasks;
    array_info associatedtasks_ai;

// Units: millisecond
    int64_t time;

    KeyValuePair** info;
    array_info info_ai;

};
typedef struct EntityState_struct EntityState;
void lmcp_pp_EntityState(EntityState* s);
size_t lmcp_packsize_EntityState (EntityState* i);
size_t lmcp_pack_EntityState_header(uint8_t* buf, EntityState* i);
void lmcp_free_EntityState(EntityState* i, int out_malloced);
void lmcp_init_EntityState (EntityState** i);
int lmcp_unpack_EntityState(uint8_t** buf, size_t *size_remain,EntityState* outp);
size_t lmcp_pack_EntityState(uint8_t* buf, EntityState* i);

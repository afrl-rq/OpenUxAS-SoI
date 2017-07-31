
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Location3D.h"
#include "PayloadState.h"
#include "enums.h"
#include "KeyValuePair.h"
#define LMCP_EntityState_SUB "afrl.cmasi.EntityState"

#define LMCP_EntityState_TYPENAME "EntityState"

#define LMCP_EntityState_TYPE 14

typedef struct {
    lmcp_object super;
    int64_t ID;

// Units: meter/sec
    float u;

// Units: meter/sec
    float v;

// Units: meter/sec
    float w;

// Units: meter/sec/sec
    float udot;

// Units: meter/sec/sec
    float vdot;

// Units: meter/sec/sec
    float wdot;

// Units: degree
    float Heading;

// Units: degree
    float Pitch;

// Units: degree
    float Roll;

// Units: degree/sec
    float p;

// Units: degree/sec
    float q;

// Units: degree/sec
    float r;

// Units: degrees
    float Course;

// Units: m/s
    float Groundspeed;

    Location3D* Location;

// Units: %
    float EnergyAvailable;

// Units: %/sec
    float ActualEnergyRate;

    PayloadState** PayloadStateList;
    array_info PayloadStateList_ai;

// Units: None
    int64_t CurrentWaypoint;

    int64_t CurrentCommand;

// Units: None
    NavigationMode Mode;

// Units: None
    int64_t* AssociatedTasks;
    array_info AssociatedTasks_ai;

// Units: millisecond
    int64_t Time;

    KeyValuePair** Info;
    array_info Info_ai;

} EntityState;
void lmcp_pp_EntityState(EntityState* s);
size_t lmcp_packsize_EntityState (EntityState* i);
size_t lmcp_pack_EntityState_header(uint8_t* buf, EntityState* i);
void lmcp_free_EntityState(EntityState* i, int out_malloced);
void lmcp_init_EntityState (EntityState** i);
int lmcp_unpack_EntityState(uint8_t** buf, size_t *size_remain,EntityState* outp);
size_t lmcp_pack_EntityState(uint8_t* buf, EntityState* i);

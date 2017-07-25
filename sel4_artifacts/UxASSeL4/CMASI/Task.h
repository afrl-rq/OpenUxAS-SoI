
#pragma once
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "KeyValuePair.h"
#define LMCP_Task_SUB "afrl.cmasi.Task"

#define LMCP_Task_TYPENAME "Task"

#define LMCP_Task_TYPE 8

typedef struct {
    lmcp_object super;
// Units: None
    int64_t TaskID;

    char* Label;
    array_info Label_ai;

// Units: None
    int64_t* EligibleEntities;
    array_info EligibleEntities_ai;

// Units: sec
    float RevisitRate;

    KeyValuePair** Parameters;
    array_info Parameters_ai;

    uint8_t Priority;

    uint8_t Required;

} Task;
void lmcp_pp_Task(Task* s);
size_t lmcp_packsize_Task (Task* i);
size_t lmcp_pack_Task_header(uint8_t* buf, Task* i);
void lmcp_free_Task(Task* i, int out_malloced);
void lmcp_init_Task (Task** i);
int lmcp_unpack_Task(uint8_t** buf, size_t *size_remain,Task* outp);
size_t lmcp_pack_Task(uint8_t* buf, Task* i);

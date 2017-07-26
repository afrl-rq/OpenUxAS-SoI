
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "EntityState.h"
#include "Location3D.h"
#include "PayloadState.h"
#include "enums.h"
#include "KeyValuePair.h"
void lmcp_pp_EntityState(EntityState* s) {
    printf("EntityState{");
    printf("ID: ");
    printf("%lld",s->ID);
    printf("\n");
    printf("u: ");
    printf("%f",s->u);
    printf("\n");
    printf("v: ");
    printf("%f",s->v);
    printf("\n");
    printf("w: ");
    printf("%f",s->w);
    printf("\n");
    printf("udot: ");
    printf("%f",s->udot);
    printf("\n");
    printf("vdot: ");
    printf("%f",s->vdot);
    printf("\n");
    printf("wdot: ");
    printf("%f",s->wdot);
    printf("\n");
    printf("Heading: ");
    printf("%f",s->Heading);
    printf("\n");
    printf("Pitch: ");
    printf("%f",s->Pitch);
    printf("\n");
    printf("Roll: ");
    printf("%f",s->Roll);
    printf("\n");
    printf("p: ");
    printf("%f",s->p);
    printf("\n");
    printf("q: ");
    printf("%f",s->q);
    printf("\n");
    printf("r: ");
    printf("%f",s->r);
    printf("\n");
    printf("Course: ");
    printf("%f",s->Course);
    printf("\n");
    printf("Groundspeed: ");
    printf("%f",s->Groundspeed);
    printf("\n");
    printf("Location: ");
    lmcp_pp_Location3D((s->Location));
    printf("\n");
    printf("EnergyAvailable: ");
    printf("%f",s->EnergyAvailable);
    printf("\n");
    printf("ActualEnergyRate: ");
    printf("%f",s->ActualEnergyRate);
    printf("\n");
    printf("PayloadStateList: ");
    printf("[");
    for (uint32_t index = 0; index < s->PayloadStateList_ai.length; index++) {
        lmcp_pp_PayloadState((s->PayloadStateList[index]));
        printf(",");
    }
    printf("\n");
    printf("CurrentWaypoint: ");
    printf("%lld",s->CurrentWaypoint);
    printf("\n");
    printf("CurrentCommand: ");
    printf("%lld",s->CurrentCommand);
    printf("\n");
    printf("Mode: ");
    printf("%i", s->Mode);
    printf("\n");
    printf("AssociatedTasks: ");
    printf("[");
    for (uint32_t index = 0; index < s->AssociatedTasks_ai.length; index++) {
        printf("%lld",s->AssociatedTasks[index]);
        printf(",");
    }
    printf("\n");
    printf("Time: ");
    printf("%lld",s->Time);
    printf("\n");
    printf("Info: ");
    printf("[");
    for (uint32_t index = 0; index < s->Info_ai.length; index++) {
        lmcp_pp_KeyValuePair((s->Info[index]));
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_EntityState (EntityState* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    if (i->Location==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_Location3D(i->Location);
    }
    out += sizeof(float);
    out += sizeof(float);
    out += 2;
    for (uint32_t index = 0; index < i->PayloadStateList_ai.length; index++) {
        out += 15 + lmcp_packsize_PayloadState(i->PayloadStateList[index]);
    }
    out += sizeof(int64_t);
    out += sizeof(int64_t);
    out += 4;
    out += 2;
    for (uint32_t index = 0; index < i->AssociatedTasks_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->Info_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->Info[index]);
    }
    return out;
}
size_t lmcp_pack_EntityState_header(uint8_t* buf, EntityState* i) {
    uint8_t* outb = buf;
    if (i == NULL) {
        lmcp_pack_uint8_t(outb, 0);
        return 1;
    }
    outb += lmcp_pack_uint8_t(outb, 1);
    memcpy(outb, "CMASI", 5);
    outb += 5;
    for (size_t j = 5; j < 8; j++, outb++)
        *outb = 0;
    outb += lmcp_pack_uint32_t(outb, 14);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_EntityState(EntityState* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->Location != NULL) {
        lmcp_free_Location3D(out->Location, 1);
    }
    if (out->PayloadStateList != NULL) {
        for (uint32_t index = 0; index < out->PayloadStateList_ai.length; index++) {
            if (out->PayloadStateList[index] != NULL) {
                lmcp_free_PayloadState(out->PayloadStateList[index], 1);
            }
        }
        free(out->PayloadStateList);
    }
    if (out->AssociatedTasks != NULL) {
        free(out->AssociatedTasks);
    }
    if (out->Info != NULL) {
        for (uint32_t index = 0; index < out->Info_ai.length; index++) {
            if (out->Info[index] != NULL) {
                lmcp_free_KeyValuePair(out->Info[index], 1);
            }
        }
        free(out->Info);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_EntityState (EntityState** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(EntityState));
    ((lmcp_object*)(*i)) -> type = 14;
}
int lmcp_unpack_EntityState(uint8_t** inb, size_t *size_remain, EntityState* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    EntityState* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->ID)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->u)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->v)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->w)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->udot)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->vdot)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->wdot)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Heading)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Pitch)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Roll)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->p)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->q)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->r)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Course)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Groundspeed)))
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->Location = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_Location3D(&(out->Location));
        CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->Location)))
    }
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->EnergyAvailable)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->ActualEnergyRate)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->PayloadStateList = malloc(sizeof(PayloadState*) * tmp);
    if (out->PayloadStateList==0) {
        return -1;
    }
    out->PayloadStateList_ai.length = tmp;
    for (uint32_t index = 0; index < out->PayloadStateList_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->PayloadStateList[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_PayloadState(&(out->PayloadStateList[index]));
            CHECK(lmcp_unpack_PayloadState(inb, size_remain, (out->PayloadStateList[index])))
        }
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->CurrentWaypoint)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->CurrentCommand)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->Mode)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->AssociatedTasks = malloc(sizeof(int64_t*) * tmp);
    if (out->AssociatedTasks==0) {
        return -1;
    }
    out->AssociatedTasks_ai.length = tmp;
    for (uint32_t index = 0; index < out->AssociatedTasks_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->AssociatedTasks[index]))
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->Time)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Info = malloc(sizeof(KeyValuePair*) * tmp);
    if (out->Info==0) {
        return -1;
    }
    out->Info_ai.length = tmp;
    for (uint32_t index = 0; index < out->Info_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->Info[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_KeyValuePair(&(out->Info[index]));
            CHECK(lmcp_unpack_KeyValuePair(inb, size_remain, (out->Info[index])))
        }
    }
    return 0;
}
size_t lmcp_pack_EntityState(uint8_t* buf, EntityState* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->ID);
    outb += lmcp_pack_float(outb, i->u);
    outb += lmcp_pack_float(outb, i->v);
    outb += lmcp_pack_float(outb, i->w);
    outb += lmcp_pack_float(outb, i->udot);
    outb += lmcp_pack_float(outb, i->vdot);
    outb += lmcp_pack_float(outb, i->wdot);
    outb += lmcp_pack_float(outb, i->Heading);
    outb += lmcp_pack_float(outb, i->Pitch);
    outb += lmcp_pack_float(outb, i->Roll);
    outb += lmcp_pack_float(outb, i->p);
    outb += lmcp_pack_float(outb, i->q);
    outb += lmcp_pack_float(outb, i->r);
    outb += lmcp_pack_float(outb, i->Course);
    outb += lmcp_pack_float(outb, i->Groundspeed);
    if (i->Location==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 3);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_Location3D(outb, i->Location);
    }
    outb += lmcp_pack_float(outb, i->EnergyAvailable);
    outb += lmcp_pack_float(outb, i->ActualEnergyRate);
    outb += lmcp_pack_uint16_t(outb, i->PayloadStateList_ai.length);
    for (uint32_t index = 0; index < i->PayloadStateList_ai.length; index++) {
        if (i->PayloadStateList[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 6);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_PayloadState(outb, i->PayloadStateList[index]);
        }
    }
    outb += lmcp_pack_int64_t(outb, i->CurrentWaypoint);
    outb += lmcp_pack_int64_t(outb, i->CurrentCommand);
    outb += lmcp_pack_int32_t(outb, (int) i->Mode);
    outb += lmcp_pack_uint16_t(outb, i->AssociatedTasks_ai.length);
    for (uint32_t index = 0; index < i->AssociatedTasks_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->AssociatedTasks[index]);
    }
    outb += lmcp_pack_int64_t(outb, i->Time);
    outb += lmcp_pack_uint16_t(outb, i->Info_ai.length);
    for (uint32_t index = 0; index < i->Info_ai.length; index++) {
        if (i->Info[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 2);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_KeyValuePair(outb, i->Info[index]);
        }
    }
    return (outb - buf);
}

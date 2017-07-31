
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Waypoint.h"
#include "Location3D.h"
#include "enums.h"
#include "VehicleAction.h"
void lmcp_pp_Waypoint(Waypoint* s) {
    printf("Waypoint{");
    printf("Inherited from Location3D:\n");
    lmcp_pp_Location3D(&(s->super));
    printf("Number: ");
    printf("%lld",s->Number);
    printf("\n");
    printf("NextWaypoint: ");
    printf("%lld",s->NextWaypoint);
    printf("\n");
    printf("Speed: ");
    printf("%f",s->Speed);
    printf("\n");
    printf("SpeedType: ");
    printf("%i", s->SpeedType);
    printf("\n");
    printf("ClimbRate: ");
    printf("%f",s->ClimbRate);
    printf("\n");
    printf("TurnType: ");
    printf("%i", s->TurnType);
    printf("\n");
    printf("VehicleActionList: ");
    printf("[");
    for (uint32_t index = 0; index < s->VehicleActionList_ai.length; index++) {
        lmcp_pp_VehicleAction((s->VehicleActionList[index]));
        printf(",");
    }
    printf("\n");
    printf("ContingencyWaypointA: ");
    printf("%lld",s->ContingencyWaypointA);
    printf("\n");
    printf("ContingencyWaypointB: ");
    printf("%lld",s->ContingencyWaypointB);
    printf("\n");
    printf("AssociatedTasks: ");
    printf("[");
    for (uint32_t index = 0; index < s->AssociatedTasks_ai.length; index++) {
        printf("%lld",s->AssociatedTasks[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_Waypoint (Waypoint* i) {
    size_t out = 0;
    out += lmcp_packsize_Location3D(&(i->super));
    out += sizeof(int64_t);
    out += sizeof(int64_t);
    out += sizeof(float);
    out += 4;
    out += sizeof(float);
    out += 4;
    out += 2;
    for (uint32_t index = 0; index < i->VehicleActionList_ai.length; index++) {
        out += 15 + lmcp_packsize_VehicleAction(i->VehicleActionList[index]);
    }
    out += sizeof(int64_t);
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->AssociatedTasks_ai.length; index++) {
        out += sizeof(int64_t);
    }
    return out;
}
size_t lmcp_pack_Waypoint_header(uint8_t* buf, Waypoint* i) {
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
    outb += lmcp_pack_uint32_t(outb, 35);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_Waypoint(Waypoint* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_Location3D(&(out->super), 0);
    if (out->VehicleActionList != NULL) {
        for (uint32_t index = 0; index < out->VehicleActionList_ai.length; index++) {
            if (out->VehicleActionList[index] != NULL) {
                lmcp_free_VehicleAction(out->VehicleActionList[index], 1);
            }
        }
        free(out->VehicleActionList);
    }
    if (out->AssociatedTasks != NULL) {
        free(out->AssociatedTasks);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_Waypoint (Waypoint** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(Waypoint));
    ((lmcp_object*)(*i)) -> type = 35;
}
int lmcp_unpack_Waypoint(uint8_t** inb, size_t *size_remain, Waypoint* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    Waypoint* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_Location3D(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->Number)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->NextWaypoint)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Speed)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->SpeedType)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->ClimbRate)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->TurnType)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->VehicleActionList = malloc(sizeof(VehicleAction*) * tmp);
    if (out->VehicleActionList==0) {
        return -1;
    }
    out->VehicleActionList_ai.length = tmp;
    for (uint32_t index = 0; index < out->VehicleActionList_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->VehicleActionList[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_VehicleAction(&(out->VehicleActionList[index]));
            CHECK(lmcp_unpack_VehicleAction(inb, size_remain, (out->VehicleActionList[index])))
        }
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->ContingencyWaypointA)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->ContingencyWaypointB)))
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
    return 0;
}
size_t lmcp_pack_Waypoint(uint8_t* buf, Waypoint* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_Location3D(outb, &(i->super));
    outb += lmcp_pack_int64_t(outb, i->Number);
    outb += lmcp_pack_int64_t(outb, i->NextWaypoint);
    outb += lmcp_pack_float(outb, i->Speed);
    outb += lmcp_pack_int32_t(outb, (int) i->SpeedType);
    outb += lmcp_pack_float(outb, i->ClimbRate);
    outb += lmcp_pack_int32_t(outb, (int) i->TurnType);
    outb += lmcp_pack_uint16_t(outb, i->VehicleActionList_ai.length);
    for (uint32_t index = 0; index < i->VehicleActionList_ai.length; index++) {
        if (i->VehicleActionList[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 7);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_VehicleAction(outb, i->VehicleActionList[index]);
        }
    }
    outb += lmcp_pack_int64_t(outb, i->ContingencyWaypointA);
    outb += lmcp_pack_int64_t(outb, i->ContingencyWaypointB);
    outb += lmcp_pack_uint16_t(outb, i->AssociatedTasks_ai.length);
    for (uint32_t index = 0; index < i->AssociatedTasks_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->AssociatedTasks[index]);
    }
    return (outb - buf);
}

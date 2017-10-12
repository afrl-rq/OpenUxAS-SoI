
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
    printf("number: ");
    printf("%lld",s->number);
    printf("\n");
    printf("nextwaypoint: ");
    printf("%lld",s->nextwaypoint);
    printf("\n");
    printf("speed: ");
    printf("%u",s->speed);
    printf("\n");
    printf("speedtype: ");
    printf("%i", s->speedtype);
    printf("\n");
    printf("climbrate: ");
    printf("%u",s->climbrate);
    printf("\n");
    printf("turntype: ");
    printf("%i", s->turntype);
    printf("\n");
    printf("vehicleactionlist: ");
    printf("[");
    for (uint32_t index = 0; index < s->vehicleactionlist_ai.length; index++) {
        lmcp_pp_VehicleAction((s->vehicleactionlist[index]));
        printf(",");
    }
    printf("\n");
    printf("contingencywaypointa: ");
    printf("%lld",s->contingencywaypointa);
    printf("\n");
    printf("contingencywaypointb: ");
    printf("%lld",s->contingencywaypointb);
    printf("\n");
    printf("associatedtasks: ");
    printf("[");
    for (uint32_t index = 0; index < s->associatedtasks_ai.length; index++) {
        printf("%lld",s->associatedtasks[index]);
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
    out += sizeof(uint32_t);
    out += 4;
    out += sizeof(uint32_t);
    out += 4;
    out += 2;
    for (uint32_t index = 0; index < i->vehicleactionlist_ai.length; index++) {
        out += 15 + lmcp_packsize_VehicleAction(i->vehicleactionlist[index]);
    }
    out += sizeof(int64_t);
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->associatedtasks_ai.length; index++) {
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
    if (out->vehicleactionlist != NULL) {
        for (uint32_t index = 0; index < out->vehicleactionlist_ai.length; index++) {
            if (out->vehicleactionlist[index] != NULL) {
                lmcp_free_VehicleAction(out->vehicleactionlist[index], 1);
            }
        }
        free(out->vehicleactionlist);
    }
    if (out->associatedtasks != NULL) {
        free(out->associatedtasks);
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
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->number)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->nextwaypoint)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->speed)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->speedtype)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->climbrate)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->turntype)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->vehicleactionlist = malloc(sizeof(VehicleAction*) * tmp);
    if (out->vehicleactionlist==0) {
        return -1;
    }
    out->vehicleactionlist_ai.length = tmp;
    for (uint32_t index = 0; index < out->vehicleactionlist_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->vehicleactionlist[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_VehicleAction(&(out->vehicleactionlist[index]));
            CHECK(lmcp_unpack_VehicleAction(inb, size_remain, (out->vehicleactionlist[index])))
        }
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->contingencywaypointa)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->contingencywaypointb)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->associatedtasks = malloc(sizeof(int64_t*) * tmp);
    if (out->associatedtasks==0) {
        return -1;
    }
    out->associatedtasks_ai.length = tmp;
    for (uint32_t index = 0; index < out->associatedtasks_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->associatedtasks[index]))
    }
    return 0;
}
size_t lmcp_pack_Waypoint(uint8_t* buf, Waypoint* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_Location3D(outb, &(i->super));
    outb += lmcp_pack_int64_t(outb, i->number);
    outb += lmcp_pack_int64_t(outb, i->nextwaypoint);
    outb += lmcp_pack_uint32_t(outb, i->speed);
    outb += lmcp_pack_int32_t(outb, (int) i->speedtype);
    outb += lmcp_pack_uint32_t(outb, i->climbrate);
    outb += lmcp_pack_int32_t(outb, (int) i->turntype);
    outb += lmcp_pack_uint16_t(outb, i->vehicleactionlist_ai.length);
    for (uint32_t index = 0; index < i->vehicleactionlist_ai.length; index++) {
        if (i->vehicleactionlist[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 7);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_VehicleAction(outb, i->vehicleactionlist[index]);
        }
    }
    outb += lmcp_pack_int64_t(outb, i->contingencywaypointa);
    outb += lmcp_pack_int64_t(outb, i->contingencywaypointb);
    outb += lmcp_pack_uint16_t(outb, i->associatedtasks_ai.length);
    for (uint32_t index = 0; index < i->associatedtasks_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->associatedtasks[index]);
    }
    return (outb - buf);
}

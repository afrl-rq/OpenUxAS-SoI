
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "WaypointTransfer.h"
#include "Waypoint.h"
#include "enums.h"
void lmcp_pp_WaypointTransfer(WaypointTransfer* s) {
    printf("WaypointTransfer{");
    printf("EntityID: ");
    printf("%lld",s->EntityID);
    printf("\n");
    printf("Waypoints: ");
    printf("[");
    for (uint32_t index = 0; index < s->Waypoints_ai.length; index++) {
        lmcp_pp_Waypoint((s->Waypoints[index]));
        printf(",");
    }
    printf("\n");
    printf("TransferMode: ");
    printf("%i", s->TransferMode);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_WaypointTransfer (WaypointTransfer* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->Waypoints_ai.length; index++) {
        out += 15 + lmcp_packsize_Waypoint(i->Waypoints[index]);
    }
    out += 4;
    return out;
}
size_t lmcp_pack_WaypointTransfer_header(uint8_t* buf, WaypointTransfer* i) {
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
    outb += lmcp_pack_uint32_t(outb, 59);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_WaypointTransfer(WaypointTransfer* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->Waypoints != NULL) {
        for (uint32_t index = 0; index < out->Waypoints_ai.length; index++) {
            if (out->Waypoints[index] != NULL) {
                lmcp_free_Waypoint(out->Waypoints[index], 1);
            }
        }
        free(out->Waypoints);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_WaypointTransfer (WaypointTransfer** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(WaypointTransfer));
    ((lmcp_object*)(*i)) -> type = 59;
}
int lmcp_unpack_WaypointTransfer(uint8_t** inb, size_t *size_remain, WaypointTransfer* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    WaypointTransfer* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->EntityID)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Waypoints = malloc(sizeof(Waypoint*) * tmp);
    if (out->Waypoints==0) {
        return -1;
    }
    out->Waypoints_ai.length = tmp;
    for (uint32_t index = 0; index < out->Waypoints_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->Waypoints[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_Waypoint(&(out->Waypoints[index]));
            CHECK(lmcp_unpack_Waypoint(inb, size_remain, (out->Waypoints[index])))
        }
    }
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->TransferMode)))
    return 0;
}
size_t lmcp_pack_WaypointTransfer(uint8_t* buf, WaypointTransfer* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->EntityID);
    outb += lmcp_pack_uint16_t(outb, i->Waypoints_ai.length);
    for (uint32_t index = 0; index < i->Waypoints_ai.length; index++) {
        if (i->Waypoints[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 35);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_Waypoint(outb, i->Waypoints[index]);
        }
    }
    outb += lmcp_pack_int32_t(outb, (int) i->TransferMode);
    return (outb - buf);
}

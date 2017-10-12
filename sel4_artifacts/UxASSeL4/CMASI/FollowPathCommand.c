
#include "common/struct_defines.h"
#include "common/conv.h"
#include "FollowPathCommand.h"
#include "VehicleActionCommand.h"
#include "PathWaypoint.h"
#include "enums.h"
void lmcp_pp_FollowPathCommand(FollowPathCommand* s) {
    printf("FollowPathCommand{");
    printf("Inherited from VehicleActionCommand:\n");
    lmcp_pp_VehicleActionCommand(&(s->super));
    printf("firstwaypoint: ");
    printf("%lld",s->firstwaypoint);
    printf("\n");
    printf("waypointlist: ");
    printf("[");
    for (uint32_t index = 0; index < s->waypointlist_ai.length; index++) {
        lmcp_pp_PathWaypoint((s->waypointlist[index]));
        printf(",");
    }
    printf("\n");
    printf("starttime: ");
    printf("%lld",s->starttime);
    printf("\n");
    printf("stoptime: ");
    printf("%lld",s->stoptime);
    printf("\n");
    printf("repeatmode: ");
    printf("%i", s->repeatmode);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_FollowPathCommand (FollowPathCommand* i) {
    size_t out = 0;
    out += lmcp_packsize_VehicleActionCommand(&(i->super));
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->waypointlist_ai.length; index++) {
        out += 15 + lmcp_packsize_PathWaypoint(i->waypointlist[index]);
    }
    out += sizeof(int64_t);
    out += sizeof(int64_t);
    out += 4;
    return out;
}
size_t lmcp_pack_FollowPathCommand_header(uint8_t* buf, FollowPathCommand* i) {
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
    outb += lmcp_pack_uint32_t(outb, 56);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_FollowPathCommand(FollowPathCommand* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_VehicleActionCommand(&(out->super), 0);
    if (out->waypointlist != NULL) {
        for (uint32_t index = 0; index < out->waypointlist_ai.length; index++) {
            if (out->waypointlist[index] != NULL) {
                lmcp_free_PathWaypoint(out->waypointlist[index], 1);
            }
        }
        free(out->waypointlist);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_FollowPathCommand (FollowPathCommand** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(FollowPathCommand));
    ((lmcp_object*)(*i)) -> type = 56;
}
int lmcp_unpack_FollowPathCommand(uint8_t** inb, size_t *size_remain, FollowPathCommand* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    FollowPathCommand* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_VehicleActionCommand(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->firstwaypoint)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->waypointlist = malloc(sizeof(PathWaypoint*) * tmp);
    if (out->waypointlist==0) {
        return -1;
    }
    out->waypointlist_ai.length = tmp;
    for (uint32_t index = 0; index < out->waypointlist_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->waypointlist[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_PathWaypoint(&(out->waypointlist[index]));
            CHECK(lmcp_unpack_PathWaypoint(inb, size_remain, (out->waypointlist[index])))
        }
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->starttime)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->stoptime)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->repeatmode)))
    return 0;
}
size_t lmcp_pack_FollowPathCommand(uint8_t* buf, FollowPathCommand* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_VehicleActionCommand(outb, &(i->super));
    outb += lmcp_pack_int64_t(outb, i->firstwaypoint);
    outb += lmcp_pack_uint16_t(outb, i->waypointlist_ai.length);
    for (uint32_t index = 0; index < i->waypointlist_ai.length; index++) {
        if (i->waypointlist[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 57);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_PathWaypoint(outb, i->waypointlist[index]);
        }
    }
    outb += lmcp_pack_int64_t(outb, i->starttime);
    outb += lmcp_pack_int64_t(outb, i->stoptime);
    outb += lmcp_pack_int32_t(outb, (int) i->repeatmode);
    return (outb - buf);
}

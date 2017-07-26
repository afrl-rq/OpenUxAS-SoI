
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "MissionCommand.h"
#include "VehicleActionCommand.h"
#include "Waypoint.h"
void lmcp_pp_MissionCommand(MissionCommand* s) {
    printf("MissionCommand{");
    printf("Inherited from VehicleActionCommand:\n");
    lmcp_pp_VehicleActionCommand(&(s->super));
    printf("WaypointList: ");
    printf("[");
    for (uint32_t index = 0; index < s->WaypointList_ai.length; index++) {
        lmcp_pp_Waypoint((s->WaypointList[index]));
        printf(",");
    }
    printf("\n");
    printf("FirstWaypoint: ");
    printf("%lld",s->FirstWaypoint);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_MissionCommand (MissionCommand* i) {
    size_t out = 0;
    out += lmcp_packsize_VehicleActionCommand(&(i->super));
    out += 2;
    for (uint32_t index = 0; index < i->WaypointList_ai.length; index++) {
        out += 15 + lmcp_packsize_Waypoint(i->WaypointList[index]);
    }
    out += sizeof(int64_t);
    return out;
}
size_t lmcp_pack_MissionCommand_header(uint8_t* buf, MissionCommand* i) {
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
    outb += lmcp_pack_uint32_t(outb, 36);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_MissionCommand(MissionCommand* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_VehicleActionCommand(&(out->super), 0);
    if (out->WaypointList != NULL) {
        for (uint32_t index = 0; index < out->WaypointList_ai.length; index++) {
            if (out->WaypointList[index] != NULL) {
                lmcp_free_Waypoint(out->WaypointList[index], 1);
            }
        }
        free(out->WaypointList);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_MissionCommand (MissionCommand** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(MissionCommand));
    ((lmcp_object*)(*i)) -> type = 36;
}
int lmcp_unpack_MissionCommand(uint8_t** inb, size_t *size_remain, MissionCommand* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    MissionCommand* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_VehicleActionCommand(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->WaypointList = malloc(sizeof(Waypoint*) * tmp);
    if (out->WaypointList==0) {
        return -1;
    }
    out->WaypointList_ai.length = tmp;
    for (uint32_t index = 0; index < out->WaypointList_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->WaypointList[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_Waypoint(&(out->WaypointList[index]));
            CHECK(lmcp_unpack_Waypoint(inb, size_remain, (out->WaypointList[index])))
        }
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->FirstWaypoint)))
    return 0;
}
size_t lmcp_pack_MissionCommand(uint8_t* buf, MissionCommand* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_VehicleActionCommand(outb, &(i->super));
    outb += lmcp_pack_uint16_t(outb, i->WaypointList_ai.length);
    for (uint32_t index = 0; index < i->WaypointList_ai.length; index++) {
        if (i->WaypointList[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 35);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_Waypoint(outb, i->WaypointList[index]);
        }
    }
    outb += lmcp_pack_int64_t(outb, i->FirstWaypoint);
    return (outb - buf);
}

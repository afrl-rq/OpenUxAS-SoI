
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AutomationResponse.h"
#include "MissionCommand.h"
#include "VehicleActionCommand.h"
#include "KeyValuePair.h"
void lmcp_pp_AutomationResponse(AutomationResponse* s) {
    printf("AutomationResponse{");
    printf("missioncommandlist: ");
    printf("[");
    for (uint32_t index = 0; index < s->missioncommandlist_ai.length; index++) {
        lmcp_pp_MissionCommand((s->missioncommandlist[index]));
        printf(",");
    }
    printf("\n");
    printf("vehiclecommandlist: ");
    printf("[");
    for (uint32_t index = 0; index < s->vehiclecommandlist_ai.length; index++) {
        lmcp_pp_VehicleActionCommand((s->vehiclecommandlist[index]));
        printf(",");
    }
    printf("\n");
    printf("info: ");
    printf("[");
    for (uint32_t index = 0; index < s->info_ai.length; index++) {
        lmcp_pp_KeyValuePair((s->info[index]));
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_AutomationResponse (AutomationResponse* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->missioncommandlist_ai.length; index++) {
        out += 15 + lmcp_packsize_MissionCommand(i->missioncommandlist[index]);
    }
    out += 2;
    for (uint32_t index = 0; index < i->vehiclecommandlist_ai.length; index++) {
        out += 15 + lmcp_packsize_VehicleActionCommand(i->vehiclecommandlist[index]);
    }
    out += 2;
    for (uint32_t index = 0; index < i->info_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->info[index]);
    }
    return out;
}
size_t lmcp_pack_AutomationResponse_header(uint8_t* buf, AutomationResponse* i) {
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
    outb += lmcp_pack_uint32_t(outb, 51);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_AutomationResponse(AutomationResponse* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->missioncommandlist != NULL) {
        for (uint32_t index = 0; index < out->missioncommandlist_ai.length; index++) {
            if (out->missioncommandlist[index] != NULL) {
                lmcp_free_MissionCommand(out->missioncommandlist[index], 1);
            }
        }
        free(out->missioncommandlist);
    }
    if (out->vehiclecommandlist != NULL) {
        for (uint32_t index = 0; index < out->vehiclecommandlist_ai.length; index++) {
            if (out->vehiclecommandlist[index] != NULL) {
                lmcp_free_VehicleActionCommand(out->vehiclecommandlist[index], 1);
            }
        }
        free(out->vehiclecommandlist);
    }
    if (out->info != NULL) {
        for (uint32_t index = 0; index < out->info_ai.length; index++) {
            if (out->info[index] != NULL) {
                lmcp_free_KeyValuePair(out->info[index], 1);
            }
        }
        free(out->info);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_AutomationResponse (AutomationResponse** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(AutomationResponse));
    ((lmcp_object*)(*i)) -> type = 51;
}
int lmcp_unpack_AutomationResponse(uint8_t** inb, size_t *size_remain, AutomationResponse* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    AutomationResponse* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->missioncommandlist = malloc(sizeof(MissionCommand*) * tmp);
    if (out->missioncommandlist==0) {
        return -1;
    }
    out->missioncommandlist_ai.length = tmp;
    for (uint32_t index = 0; index < out->missioncommandlist_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->missioncommandlist[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_MissionCommand(&(out->missioncommandlist[index]));
            CHECK(lmcp_unpack_MissionCommand(inb, size_remain, (out->missioncommandlist[index])))
        }
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->vehiclecommandlist = malloc(sizeof(VehicleActionCommand*) * tmp);
    if (out->vehiclecommandlist==0) {
        return -1;
    }
    out->vehiclecommandlist_ai.length = tmp;
    for (uint32_t index = 0; index < out->vehiclecommandlist_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->vehiclecommandlist[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_VehicleActionCommand(&(out->vehiclecommandlist[index]));
            CHECK(lmcp_unpack_VehicleActionCommand(inb, size_remain, (out->vehiclecommandlist[index])))
        }
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->info = malloc(sizeof(KeyValuePair*) * tmp);
    if (out->info==0) {
        return -1;
    }
    out->info_ai.length = tmp;
    for (uint32_t index = 0; index < out->info_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->info[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_KeyValuePair(&(out->info[index]));
            CHECK(lmcp_unpack_KeyValuePair(inb, size_remain, (out->info[index])))
        }
    }
    return 0;
}
size_t lmcp_pack_AutomationResponse(uint8_t* buf, AutomationResponse* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->missioncommandlist_ai.length);
    for (uint32_t index = 0; index < i->missioncommandlist_ai.length; index++) {
        if (i->missioncommandlist[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 36);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_MissionCommand(outb, i->missioncommandlist[index]);
        }
    }
    outb += lmcp_pack_uint16_t(outb, i->vehiclecommandlist_ai.length);
    for (uint32_t index = 0; index < i->vehiclecommandlist_ai.length; index++) {
        if (i->vehiclecommandlist[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 47);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_VehicleActionCommand(outb, i->vehiclecommandlist[index]);
        }
    }
    outb += lmcp_pack_uint16_t(outb, i->info_ai.length);
    for (uint32_t index = 0; index < i->info_ai.length; index++) {
        if (i->info[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 2);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_KeyValuePair(outb, i->info[index]);
        }
    }
    return (outb - buf);
}


#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AutomationResponse.h"
#include "MissionCommand.h"
#include "VehicleActionCommand.h"
#include "KeyValuePair.h"
void lmcp_pp_AutomationResponse(AutomationResponse* s) {
    printf("AutomationResponse{");
    printf("MissionCommandList: ");
    printf("[");
    for (uint32_t index = 0; index < s->MissionCommandList_ai.length; index++) {
        lmcp_pp_MissionCommand((s->MissionCommandList[index]));
        printf(",");
    }
    printf("\n");
    printf("VehicleCommandList: ");
    printf("[");
    for (uint32_t index = 0; index < s->VehicleCommandList_ai.length; index++) {
        lmcp_pp_VehicleActionCommand((s->VehicleCommandList[index]));
        printf(",");
    }
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
size_t lmcp_packsize_AutomationResponse (AutomationResponse* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->MissionCommandList_ai.length; index++) {
        out += 15 + lmcp_packsize_MissionCommand(i->MissionCommandList[index]);
    }
    out += 2;
    for (uint32_t index = 0; index < i->VehicleCommandList_ai.length; index++) {
        out += 15 + lmcp_packsize_VehicleActionCommand(i->VehicleCommandList[index]);
    }
    out += 2;
    for (uint32_t index = 0; index < i->Info_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->Info[index]);
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
    if (out->MissionCommandList != NULL) {
        for (uint32_t index = 0; index < out->MissionCommandList_ai.length; index++) {
            if (out->MissionCommandList[index] != NULL) {
                lmcp_free_MissionCommand(out->MissionCommandList[index], 1);
            }
        }
        free(out->MissionCommandList);
    }
    if (out->VehicleCommandList != NULL) {
        for (uint32_t index = 0; index < out->VehicleCommandList_ai.length; index++) {
            if (out->VehicleCommandList[index] != NULL) {
                lmcp_free_VehicleActionCommand(out->VehicleCommandList[index], 1);
            }
        }
        free(out->VehicleCommandList);
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
    (out)->MissionCommandList = malloc(sizeof(MissionCommand*) * tmp);
    if (out->MissionCommandList==0) {
        return -1;
    }
    out->MissionCommandList_ai.length = tmp;
    for (uint32_t index = 0; index < out->MissionCommandList_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->MissionCommandList[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_MissionCommand(&(out->MissionCommandList[index]));
            CHECK(lmcp_unpack_MissionCommand(inb, size_remain, (out->MissionCommandList[index])))
        }
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->VehicleCommandList = malloc(sizeof(VehicleActionCommand*) * tmp);
    if (out->VehicleCommandList==0) {
        return -1;
    }
    out->VehicleCommandList_ai.length = tmp;
    for (uint32_t index = 0; index < out->VehicleCommandList_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->VehicleCommandList[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_VehicleActionCommand(&(out->VehicleCommandList[index]));
            CHECK(lmcp_unpack_VehicleActionCommand(inb, size_remain, (out->VehicleCommandList[index])))
        }
    }
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
size_t lmcp_pack_AutomationResponse(uint8_t* buf, AutomationResponse* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->MissionCommandList_ai.length);
    for (uint32_t index = 0; index < i->MissionCommandList_ai.length; index++) {
        if (i->MissionCommandList[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 36);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_MissionCommand(outb, i->MissionCommandList[index]);
        }
    }
    outb += lmcp_pack_uint16_t(outb, i->VehicleCommandList_ai.length);
    for (uint32_t index = 0; index < i->VehicleCommandList_ai.length; index++) {
        if (i->VehicleCommandList[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 47);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_VehicleActionCommand(outb, i->VehicleCommandList[index]);
        }
    }
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


#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "EntityConfiguration.h"
#include "enums.h"
#include "PayloadConfiguration.h"
#include "KeyValuePair.h"
void lmcp_pp_EntityConfiguration(EntityConfiguration* s) {
    printf("EntityConfiguration{");
    printf("ID: ");
    printf("%lld",s->ID);
    printf("\n");
    printf("Affiliation: ");
    printf("[");
    for (uint32_t index = 0; index < s->Affiliation_ai.length; index++) {
        printf("%c",s->Affiliation[index]);
        printf(",");
    }
    printf("\n");
    printf("EntityType: ");
    printf("[");
    for (uint32_t index = 0; index < s->EntityType_ai.length; index++) {
        printf("%c",s->EntityType[index]);
        printf(",");
    }
    printf("\n");
    printf("Label: ");
    printf("[");
    for (uint32_t index = 0; index < s->Label_ai.length; index++) {
        printf("%c",s->Label[index]);
        printf(",");
    }
    printf("\n");
    printf("NominalSpeed: ");
    printf("%f",s->NominalSpeed);
    printf("\n");
    printf("NominalAltitude: ");
    printf("%f",s->NominalAltitude);
    printf("\n");
    printf("NominalAltitudeType: ");
    printf("%i", s->NominalAltitudeType);
    printf("\n");
    printf("PayloadConfigurationList: ");
    printf("[");
    for (uint32_t index = 0; index < s->PayloadConfigurationList_ai.length; index++) {
        lmcp_pp_PayloadConfiguration((s->PayloadConfigurationList[index]));
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
size_t lmcp_packsize_EntityConfiguration (EntityConfiguration* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->Affiliation_ai.length; index++) {
        out += sizeof(char);
    }
    out += 2;
    for (uint32_t index = 0; index < i->EntityType_ai.length; index++) {
        out += sizeof(char);
    }
    out += 2;
    for (uint32_t index = 0; index < i->Label_ai.length; index++) {
        out += sizeof(char);
    }
    out += sizeof(float);
    out += sizeof(float);
    out += 4;
    out += 2;
    for (uint32_t index = 0; index < i->PayloadConfigurationList_ai.length; index++) {
        out += 15 + lmcp_packsize_PayloadConfiguration(i->PayloadConfigurationList[index]);
    }
    out += 2;
    for (uint32_t index = 0; index < i->Info_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->Info[index]);
    }
    return out;
}
size_t lmcp_pack_EntityConfiguration_header(uint8_t* buf, EntityConfiguration* i) {
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
    outb += lmcp_pack_uint32_t(outb, 11);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_EntityConfiguration(EntityConfiguration* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->Affiliation != NULL) {
        free(out->Affiliation);
    }
    if (out->EntityType != NULL) {
        free(out->EntityType);
    }
    if (out->Label != NULL) {
        free(out->Label);
    }
    if (out->PayloadConfigurationList != NULL) {
        for (uint32_t index = 0; index < out->PayloadConfigurationList_ai.length; index++) {
            if (out->PayloadConfigurationList[index] != NULL) {
                lmcp_free_PayloadConfiguration(out->PayloadConfigurationList[index], 1);
            }
        }
        free(out->PayloadConfigurationList);
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
void lmcp_init_EntityConfiguration (EntityConfiguration** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(EntityConfiguration));
    ((lmcp_object*)(*i)) -> type = 11;
}
int lmcp_unpack_EntityConfiguration(uint8_t** inb, size_t *size_remain, EntityConfiguration* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    EntityConfiguration* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->ID)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Affiliation = malloc(sizeof(char*) * tmp);
    if (out->Affiliation==0) {
        return -1;
    }
    out->Affiliation_ai.length = tmp;
    for (uint32_t index = 0; index < out->Affiliation_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->Affiliation[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->EntityType = malloc(sizeof(char*) * tmp);
    if (out->EntityType==0) {
        return -1;
    }
    out->EntityType_ai.length = tmp;
    for (uint32_t index = 0; index < out->EntityType_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->EntityType[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Label = malloc(sizeof(char*) * tmp);
    if (out->Label==0) {
        return -1;
    }
    out->Label_ai.length = tmp;
    for (uint32_t index = 0; index < out->Label_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->Label[index]))
    }
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->NominalSpeed)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->NominalAltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->NominalAltitudeType)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->PayloadConfigurationList = malloc(sizeof(PayloadConfiguration*) * tmp);
    if (out->PayloadConfigurationList==0) {
        return -1;
    }
    out->PayloadConfigurationList_ai.length = tmp;
    for (uint32_t index = 0; index < out->PayloadConfigurationList_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->PayloadConfigurationList[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_PayloadConfiguration(&(out->PayloadConfigurationList[index]));
            CHECK(lmcp_unpack_PayloadConfiguration(inb, size_remain, (out->PayloadConfigurationList[index])))
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
size_t lmcp_pack_EntityConfiguration(uint8_t* buf, EntityConfiguration* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->ID);
    outb += lmcp_pack_uint16_t(outb, i->Affiliation_ai.length);
    for (uint32_t index = 0; index < i->Affiliation_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->Affiliation[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->EntityType_ai.length);
    for (uint32_t index = 0; index < i->EntityType_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->EntityType[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->Label_ai.length);
    for (uint32_t index = 0; index < i->Label_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->Label[index]);
    }
    outb += lmcp_pack_float(outb, i->NominalSpeed);
    outb += lmcp_pack_float(outb, i->NominalAltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->NominalAltitudeType);
    outb += lmcp_pack_uint16_t(outb, i->PayloadConfigurationList_ai.length);
    for (uint32_t index = 0; index < i->PayloadConfigurationList_ai.length; index++) {
        if (i->PayloadConfigurationList[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 5);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_PayloadConfiguration(outb, i->PayloadConfigurationList[index]);
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

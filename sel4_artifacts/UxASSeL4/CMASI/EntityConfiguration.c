
#include "common/struct_defines.h"
#include "common/conv.h"
#include "EntityConfiguration.h"
#include "enums.h"
#include "PayloadConfiguration.h"
#include "KeyValuePair.h"
void lmcp_pp_EntityConfiguration(EntityConfiguration* s) {
    printf("EntityConfiguration{");
    printf("id: ");
    printf("%lld",s->id);
    printf("\n");
    printf("affiliation: ");
    printf("[");
    for (uint32_t index = 0; index < s->affiliation_ai.length; index++) {
        printf("%c",s->affiliation[index]);
        printf(",");
    }
    printf("\n");
    printf("entitytype: ");
    printf("[");
    for (uint32_t index = 0; index < s->entitytype_ai.length; index++) {
        printf("%c",s->entitytype[index]);
        printf(",");
    }
    printf("\n");
    printf("label: ");
    printf("[");
    for (uint32_t index = 0; index < s->label_ai.length; index++) {
        printf("%c",s->label[index]);
        printf(",");
    }
    printf("\n");
    printf("nominalspeed: ");
    printf("%u",s->nominalspeed);
    printf("\n");
    printf("nominalaltitude: ");
    printf("%u",s->nominalaltitude);
    printf("\n");
    printf("nominalaltitudetype: ");
    printf("%i", s->nominalaltitudetype);
    printf("\n");
    printf("payloadconfigurationlist: ");
    printf("[");
    for (uint32_t index = 0; index < s->payloadconfigurationlist_ai.length; index++) {
        lmcp_pp_PayloadConfiguration((s->payloadconfigurationlist[index]));
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
size_t lmcp_packsize_EntityConfiguration (EntityConfiguration* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->affiliation_ai.length; index++) {
        out += sizeof(char);
    }
    out += 2;
    for (uint32_t index = 0; index < i->entitytype_ai.length; index++) {
        out += sizeof(char);
    }
    out += 2;
    for (uint32_t index = 0; index < i->label_ai.length; index++) {
        out += sizeof(char);
    }
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += 4;
    out += 2;
    for (uint32_t index = 0; index < i->payloadconfigurationlist_ai.length; index++) {
        out += 15 + lmcp_packsize_PayloadConfiguration(i->payloadconfigurationlist[index]);
    }
    out += 2;
    for (uint32_t index = 0; index < i->info_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->info[index]);
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
    if (out->affiliation != NULL) {
        free(out->affiliation);
    }
    if (out->entitytype != NULL) {
        free(out->entitytype);
    }
    if (out->label != NULL) {
        free(out->label);
    }
    if (out->payloadconfigurationlist != NULL) {
        for (uint32_t index = 0; index < out->payloadconfigurationlist_ai.length; index++) {
            if (out->payloadconfigurationlist[index] != NULL) {
                lmcp_free_PayloadConfiguration(out->payloadconfigurationlist[index], 1);
            }
        }
        free(out->payloadconfigurationlist);
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
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->id)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->affiliation = malloc(sizeof(char*) * tmp);
    if (out->affiliation==0) {
        return -1;
    }
    out->affiliation_ai.length = tmp;
    for (uint32_t index = 0; index < out->affiliation_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->affiliation[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->entitytype = malloc(sizeof(char*) * tmp);
    if (out->entitytype==0) {
        return -1;
    }
    out->entitytype_ai.length = tmp;
    for (uint32_t index = 0; index < out->entitytype_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->entitytype[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->label = malloc(sizeof(char*) * tmp);
    if (out->label==0) {
        return -1;
    }
    out->label_ai.length = tmp;
    for (uint32_t index = 0; index < out->label_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->label[index]))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->nominalspeed)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->nominalaltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->nominalaltitudetype)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->payloadconfigurationlist = malloc(sizeof(PayloadConfiguration*) * tmp);
    if (out->payloadconfigurationlist==0) {
        return -1;
    }
    out->payloadconfigurationlist_ai.length = tmp;
    for (uint32_t index = 0; index < out->payloadconfigurationlist_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->payloadconfigurationlist[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_PayloadConfiguration(&(out->payloadconfigurationlist[index]));
            CHECK(lmcp_unpack_PayloadConfiguration(inb, size_remain, (out->payloadconfigurationlist[index])))
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
size_t lmcp_pack_EntityConfiguration(uint8_t* buf, EntityConfiguration* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->id);
    outb += lmcp_pack_uint16_t(outb, i->affiliation_ai.length);
    for (uint32_t index = 0; index < i->affiliation_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->affiliation[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->entitytype_ai.length);
    for (uint32_t index = 0; index < i->entitytype_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->entitytype[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->label_ai.length);
    for (uint32_t index = 0; index < i->label_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->label[index]);
    }
    outb += lmcp_pack_uint32_t(outb, i->nominalspeed);
    outb += lmcp_pack_uint32_t(outb, i->nominalaltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->nominalaltitudetype);
    outb += lmcp_pack_uint16_t(outb, i->payloadconfigurationlist_ai.length);
    for (uint32_t index = 0; index < i->payloadconfigurationlist_ai.length; index++) {
        if (i->payloadconfigurationlist[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 5);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_PayloadConfiguration(outb, i->payloadconfigurationlist[index]);
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

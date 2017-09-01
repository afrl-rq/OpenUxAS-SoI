
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AirVehicleConfiguration.h"
#include "EntityConfiguration.h"
#include "FlightProfile.h"
#include "FlightProfile.h"
#include "enums.h"
void lmcp_pp_AirVehicleConfiguration(AirVehicleConfiguration* s) {
    printf("AirVehicleConfiguration{");
    printf("Inherited from EntityConfiguration:\n");
    lmcp_pp_EntityConfiguration(&(s->super));
    printf("minimumspeed: ");
    printf("%u",s->minimumspeed);
    printf("\n");
    printf("maximumspeed: ");
    printf("%u",s->maximumspeed);
    printf("\n");
    printf("nominalflightprofile: ");
    lmcp_pp_FlightProfile((s->nominalflightprofile));
    printf("\n");
    printf("alternateflightprofiles: ");
    printf("[");
    for (uint32_t index = 0; index < s->alternateflightprofiles_ai.length; index++) {
        lmcp_pp_FlightProfile((s->alternateflightprofiles[index]));
        printf(",");
    }
    printf("\n");
    printf("availableloitertypes: ");
    printf("[");
    for (uint32_t index = 0; index < s->availableloitertypes_ai.length; index++) {
        printf("%i", s->availableloitertypes[index]);
        printf(",");
    }
    printf("\n");
    printf("availableturntypes: ");
    printf("[");
    for (uint32_t index = 0; index < s->availableturntypes_ai.length; index++) {
        printf("%i", s->availableturntypes[index]);
        printf(",");
    }
    printf("\n");
    printf("minimumaltitude: ");
    printf("%u",s->minimumaltitude);
    printf("\n");
    printf("minaltitudetype: ");
    printf("%i", s->minaltitudetype);
    printf("\n");
    printf("maximumaltitude: ");
    printf("%u",s->maximumaltitude);
    printf("\n");
    printf("maxaltitudetype: ");
    printf("%i", s->maxaltitudetype);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_AirVehicleConfiguration (AirVehicleConfiguration* i) {
    size_t out = 0;
    out += lmcp_packsize_EntityConfiguration(&(i->super));
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    if (i->nominalflightprofile==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_FlightProfile(i->nominalflightprofile);
    }
    out += 2;
    for (uint32_t index = 0; index < i->alternateflightprofiles_ai.length; index++) {
        out += 15 + lmcp_packsize_FlightProfile(i->alternateflightprofiles[index]);
    }
    out += 2;
    for (uint32_t index = 0; index < i->availableloitertypes_ai.length; index++) {
        out += 4;
    }
    out += 2;
    for (uint32_t index = 0; index < i->availableturntypes_ai.length; index++) {
        out += 4;
    }
    out += sizeof(uint32_t);
    out += 4;
    out += sizeof(uint32_t);
    out += 4;
    return out;
}
size_t lmcp_pack_AirVehicleConfiguration_header(uint8_t* buf, AirVehicleConfiguration* i) {
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
    outb += lmcp_pack_uint32_t(outb, 13);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_AirVehicleConfiguration(AirVehicleConfiguration* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_EntityConfiguration(&(out->super), 0);
    if (out->nominalflightprofile != NULL) {
        lmcp_free_FlightProfile(out->nominalflightprofile, 1);
    }
    if (out->alternateflightprofiles != NULL) {
        for (uint32_t index = 0; index < out->alternateflightprofiles_ai.length; index++) {
            if (out->alternateflightprofiles[index] != NULL) {
                lmcp_free_FlightProfile(out->alternateflightprofiles[index], 1);
            }
        }
        free(out->alternateflightprofiles);
    }
    if (out->availableloitertypes != NULL) {
        free(out->availableloitertypes);
    }
    if (out->availableturntypes != NULL) {
        free(out->availableturntypes);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_AirVehicleConfiguration (AirVehicleConfiguration** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(AirVehicleConfiguration));
    ((lmcp_object*)(*i)) -> type = 13;
}
int lmcp_unpack_AirVehicleConfiguration(uint8_t** inb, size_t *size_remain, AirVehicleConfiguration* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    AirVehicleConfiguration* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_EntityConfiguration(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->minimumspeed)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maximumspeed)))
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->nominalflightprofile = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_FlightProfile(&(out->nominalflightprofile));
        CHECK(lmcp_unpack_FlightProfile(inb, size_remain, (out->nominalflightprofile)))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->alternateflightprofiles = malloc(sizeof(FlightProfile*) * tmp);
    if (out->alternateflightprofiles==0) {
        return -1;
    }
    out->alternateflightprofiles_ai.length = tmp;
    for (uint32_t index = 0; index < out->alternateflightprofiles_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->alternateflightprofiles[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_FlightProfile(&(out->alternateflightprofiles[index]));
            CHECK(lmcp_unpack_FlightProfile(inb, size_remain, (out->alternateflightprofiles[index])))
        }
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->availableloitertypes = malloc(sizeof(int32_t*) * tmp);
    if (out->availableloitertypes==0) {
        return -1;
    }
    out->availableloitertypes_ai.length = tmp;
    for (uint32_t index = 0; index < out->availableloitertypes_ai.length; index++) {
        CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &out->availableloitertypes[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->availableturntypes = malloc(sizeof(int32_t*) * tmp);
    if (out->availableturntypes==0) {
        return -1;
    }
    out->availableturntypes_ai.length = tmp;
    for (uint32_t index = 0; index < out->availableturntypes_ai.length; index++) {
        CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &out->availableturntypes[index]))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->minimumaltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->minaltitudetype)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maximumaltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->maxaltitudetype)))
    return 0;
}
size_t lmcp_pack_AirVehicleConfiguration(uint8_t* buf, AirVehicleConfiguration* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_EntityConfiguration(outb, &(i->super));
    outb += lmcp_pack_uint32_t(outb, i->minimumspeed);
    outb += lmcp_pack_uint32_t(outb, i->maximumspeed);
    if (i->nominalflightprofile==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 12);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_FlightProfile(outb, i->nominalflightprofile);
    }
    outb += lmcp_pack_uint16_t(outb, i->alternateflightprofiles_ai.length);
    for (uint32_t index = 0; index < i->alternateflightprofiles_ai.length; index++) {
        if (i->alternateflightprofiles[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 12);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_FlightProfile(outb, i->alternateflightprofiles[index]);
        }
    }
    outb += lmcp_pack_uint16_t(outb, i->availableloitertypes_ai.length);
    for (uint32_t index = 0; index < i->availableloitertypes_ai.length; index++) {
        outb += lmcp_pack_int32_t(outb, (int) i->availableloitertypes[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->availableturntypes_ai.length);
    for (uint32_t index = 0; index < i->availableturntypes_ai.length; index++) {
        outb += lmcp_pack_int32_t(outb, (int) i->availableturntypes[index]);
    }
    outb += lmcp_pack_uint32_t(outb, i->minimumaltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->minaltitudetype);
    outb += lmcp_pack_uint32_t(outb, i->maximumaltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->maxaltitudetype);
    return (outb - buf);
}

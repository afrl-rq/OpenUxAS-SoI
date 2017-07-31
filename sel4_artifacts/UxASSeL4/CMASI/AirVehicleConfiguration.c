
#include <stdlib.h>
#include <inttypes.h>
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
    printf("MinimumSpeed: ");
    printf("%f",s->MinimumSpeed);
    printf("\n");
    printf("MaximumSpeed: ");
    printf("%f",s->MaximumSpeed);
    printf("\n");
    printf("NominalFlightProfile: ");
    lmcp_pp_FlightProfile((s->NominalFlightProfile));
    printf("\n");
    printf("AlternateFlightProfiles: ");
    printf("[");
    for (uint32_t index = 0; index < s->AlternateFlightProfiles_ai.length; index++) {
        lmcp_pp_FlightProfile((s->AlternateFlightProfiles[index]));
        printf(",");
    }
    printf("\n");
    printf("AvailableLoiterTypes: ");
    printf("[");
    for (uint32_t index = 0; index < s->AvailableLoiterTypes_ai.length; index++) {
        printf("%i", s->AvailableLoiterTypes[index]);
        printf(",");
    }
    printf("\n");
    printf("AvailableTurnTypes: ");
    printf("[");
    for (uint32_t index = 0; index < s->AvailableTurnTypes_ai.length; index++) {
        printf("%i", s->AvailableTurnTypes[index]);
        printf(",");
    }
    printf("\n");
    printf("MinimumAltitude: ");
    printf("%f",s->MinimumAltitude);
    printf("\n");
    printf("MinAltitudeType: ");
    printf("%i", s->MinAltitudeType);
    printf("\n");
    printf("MaximumAltitude: ");
    printf("%f",s->MaximumAltitude);
    printf("\n");
    printf("MaxAltitudeType: ");
    printf("%i", s->MaxAltitudeType);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_AirVehicleConfiguration (AirVehicleConfiguration* i) {
    size_t out = 0;
    out += lmcp_packsize_EntityConfiguration(&(i->super));
    out += sizeof(float);
    out += sizeof(float);
    if (i->NominalFlightProfile==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_FlightProfile(i->NominalFlightProfile);
    }
    out += 2;
    for (uint32_t index = 0; index < i->AlternateFlightProfiles_ai.length; index++) {
        out += 15 + lmcp_packsize_FlightProfile(i->AlternateFlightProfiles[index]);
    }
    out += 2;
    for (uint32_t index = 0; index < i->AvailableLoiterTypes_ai.length; index++) {
        out += 4;
    }
    out += 2;
    for (uint32_t index = 0; index < i->AvailableTurnTypes_ai.length; index++) {
        out += 4;
    }
    out += sizeof(float);
    out += 4;
    out += sizeof(float);
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
    if (out->NominalFlightProfile != NULL) {
        lmcp_free_FlightProfile(out->NominalFlightProfile, 1);
    }
    if (out->AlternateFlightProfiles != NULL) {
        for (uint32_t index = 0; index < out->AlternateFlightProfiles_ai.length; index++) {
            if (out->AlternateFlightProfiles[index] != NULL) {
                lmcp_free_FlightProfile(out->AlternateFlightProfiles[index], 1);
            }
        }
        free(out->AlternateFlightProfiles);
    }
    if (out->AvailableLoiterTypes != NULL) {
        free(out->AvailableLoiterTypes);
    }
    if (out->AvailableTurnTypes != NULL) {
        free(out->AvailableTurnTypes);
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
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MinimumSpeed)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaximumSpeed)))
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->NominalFlightProfile = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_FlightProfile(&(out->NominalFlightProfile));
        CHECK(lmcp_unpack_FlightProfile(inb, size_remain, (out->NominalFlightProfile)))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->AlternateFlightProfiles = malloc(sizeof(FlightProfile*) * tmp);
    if (out->AlternateFlightProfiles==0) {
        return -1;
    }
    out->AlternateFlightProfiles_ai.length = tmp;
    for (uint32_t index = 0; index < out->AlternateFlightProfiles_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->AlternateFlightProfiles[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_FlightProfile(&(out->AlternateFlightProfiles[index]));
            CHECK(lmcp_unpack_FlightProfile(inb, size_remain, (out->AlternateFlightProfiles[index])))
        }
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->AvailableLoiterTypes = malloc(sizeof(int32_t*) * tmp);
    if (out->AvailableLoiterTypes==0) {
        return -1;
    }
    out->AvailableLoiterTypes_ai.length = tmp;
    for (uint32_t index = 0; index < out->AvailableLoiterTypes_ai.length; index++) {
        CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &out->AvailableLoiterTypes[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->AvailableTurnTypes = malloc(sizeof(int32_t*) * tmp);
    if (out->AvailableTurnTypes==0) {
        return -1;
    }
    out->AvailableTurnTypes_ai.length = tmp;
    for (uint32_t index = 0; index < out->AvailableTurnTypes_ai.length; index++) {
        CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &out->AvailableTurnTypes[index]))
    }
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MinimumAltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->MinAltitudeType)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaximumAltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->MaxAltitudeType)))
    return 0;
}
size_t lmcp_pack_AirVehicleConfiguration(uint8_t* buf, AirVehicleConfiguration* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_EntityConfiguration(outb, &(i->super));
    outb += lmcp_pack_float(outb, i->MinimumSpeed);
    outb += lmcp_pack_float(outb, i->MaximumSpeed);
    if (i->NominalFlightProfile==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 12);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_FlightProfile(outb, i->NominalFlightProfile);
    }
    outb += lmcp_pack_uint16_t(outb, i->AlternateFlightProfiles_ai.length);
    for (uint32_t index = 0; index < i->AlternateFlightProfiles_ai.length; index++) {
        if (i->AlternateFlightProfiles[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 12);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_FlightProfile(outb, i->AlternateFlightProfiles[index]);
        }
    }
    outb += lmcp_pack_uint16_t(outb, i->AvailableLoiterTypes_ai.length);
    for (uint32_t index = 0; index < i->AvailableLoiterTypes_ai.length; index++) {
        outb += lmcp_pack_int32_t(outb, (int) i->AvailableLoiterTypes[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->AvailableTurnTypes_ai.length);
    for (uint32_t index = 0; index < i->AvailableTurnTypes_ai.length; index++) {
        outb += lmcp_pack_int32_t(outb, (int) i->AvailableTurnTypes[index]);
    }
    outb += lmcp_pack_float(outb, i->MinimumAltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->MinAltitudeType);
    outb += lmcp_pack_float(outb, i->MaximumAltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->MaxAltitudeType);
    return (outb - buf);
}

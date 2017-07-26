
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "GimbalConfiguration.h"
#include "PayloadConfiguration.h"
#include "enums.h"
void lmcp_pp_GimbalConfiguration(GimbalConfiguration* s) {
    printf("GimbalConfiguration{");
    printf("Inherited from PayloadConfiguration:\n");
    lmcp_pp_PayloadConfiguration(&(s->super));
    printf("SupportedPointingModes: ");
    printf("[");
    for (uint32_t index = 0; index < s->SupportedPointingModes_ai.length; index++) {
        printf("%i", s->SupportedPointingModes[index]);
        printf(",");
    }
    printf("\n");
    printf("MinAzimuth: ");
    printf("%f",s->MinAzimuth);
    printf("\n");
    printf("MaxAzimuth: ");
    printf("%f",s->MaxAzimuth);
    printf("\n");
    printf("IsAzimuthClamped: ");
    printf("%u",s->IsAzimuthClamped);
    printf("\n");
    printf("MinElevation: ");
    printf("%f",s->MinElevation);
    printf("\n");
    printf("MaxElevation: ");
    printf("%f",s->MaxElevation);
    printf("\n");
    printf("IsElevationClamped: ");
    printf("%u",s->IsElevationClamped);
    printf("\n");
    printf("MinRotation: ");
    printf("%f",s->MinRotation);
    printf("\n");
    printf("MaxRotation: ");
    printf("%f",s->MaxRotation);
    printf("\n");
    printf("IsRotationClamped: ");
    printf("%u",s->IsRotationClamped);
    printf("\n");
    printf("MaxAzimuthSlewRate: ");
    printf("%f",s->MaxAzimuthSlewRate);
    printf("\n");
    printf("MaxElevationSlewRate: ");
    printf("%f",s->MaxElevationSlewRate);
    printf("\n");
    printf("MaxRotationRate: ");
    printf("%f",s->MaxRotationRate);
    printf("\n");
    printf("ContainedPayloadList: ");
    printf("[");
    for (uint32_t index = 0; index < s->ContainedPayloadList_ai.length; index++) {
        printf("%lld",s->ContainedPayloadList[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_GimbalConfiguration (GimbalConfiguration* i) {
    size_t out = 0;
    out += lmcp_packsize_PayloadConfiguration(&(i->super));
    out += 2;
    for (uint32_t index = 0; index < i->SupportedPointingModes_ai.length; index++) {
        out += 4;
    }
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(uint8_t);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(uint8_t);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(uint8_t);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += 2;
    for (uint32_t index = 0; index < i->ContainedPayloadList_ai.length; index++) {
        out += sizeof(int64_t);
    }
    return out;
}
size_t lmcp_pack_GimbalConfiguration_header(uint8_t* buf, GimbalConfiguration* i) {
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
    outb += lmcp_pack_uint32_t(outb, 24);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_GimbalConfiguration(GimbalConfiguration* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_PayloadConfiguration(&(out->super), 0);
    if (out->SupportedPointingModes != NULL) {
        free(out->SupportedPointingModes);
    }
    if (out->ContainedPayloadList != NULL) {
        free(out->ContainedPayloadList);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_GimbalConfiguration (GimbalConfiguration** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(GimbalConfiguration));
    ((lmcp_object*)(*i)) -> type = 24;
}
int lmcp_unpack_GimbalConfiguration(uint8_t** inb, size_t *size_remain, GimbalConfiguration* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    GimbalConfiguration* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_PayloadConfiguration(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->SupportedPointingModes = malloc(sizeof(int32_t*) * tmp);
    if (out->SupportedPointingModes==0) {
        return -1;
    }
    out->SupportedPointingModes_ai.length = tmp;
    for (uint32_t index = 0; index < out->SupportedPointingModes_ai.length; index++) {
        CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &out->SupportedPointingModes[index]))
    }
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MinAzimuth)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaxAzimuth)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->IsAzimuthClamped)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MinElevation)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaxElevation)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->IsElevationClamped)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MinRotation)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaxRotation)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->IsRotationClamped)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaxAzimuthSlewRate)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaxElevationSlewRate)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaxRotationRate)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->ContainedPayloadList = malloc(sizeof(int64_t*) * tmp);
    if (out->ContainedPayloadList==0) {
        return -1;
    }
    out->ContainedPayloadList_ai.length = tmp;
    for (uint32_t index = 0; index < out->ContainedPayloadList_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->ContainedPayloadList[index]))
    }
    return 0;
}
size_t lmcp_pack_GimbalConfiguration(uint8_t* buf, GimbalConfiguration* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_PayloadConfiguration(outb, &(i->super));
    outb += lmcp_pack_uint16_t(outb, i->SupportedPointingModes_ai.length);
    for (uint32_t index = 0; index < i->SupportedPointingModes_ai.length; index++) {
        outb += lmcp_pack_int32_t(outb, (int) i->SupportedPointingModes[index]);
    }
    outb += lmcp_pack_float(outb, i->MinAzimuth);
    outb += lmcp_pack_float(outb, i->MaxAzimuth);
    outb += lmcp_pack_uint8_t(outb, i->IsAzimuthClamped);
    outb += lmcp_pack_float(outb, i->MinElevation);
    outb += lmcp_pack_float(outb, i->MaxElevation);
    outb += lmcp_pack_uint8_t(outb, i->IsElevationClamped);
    outb += lmcp_pack_float(outb, i->MinRotation);
    outb += lmcp_pack_float(outb, i->MaxRotation);
    outb += lmcp_pack_uint8_t(outb, i->IsRotationClamped);
    outb += lmcp_pack_float(outb, i->MaxAzimuthSlewRate);
    outb += lmcp_pack_float(outb, i->MaxElevationSlewRate);
    outb += lmcp_pack_float(outb, i->MaxRotationRate);
    outb += lmcp_pack_uint16_t(outb, i->ContainedPayloadList_ai.length);
    for (uint32_t index = 0; index < i->ContainedPayloadList_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->ContainedPayloadList[index]);
    }
    return (outb - buf);
}

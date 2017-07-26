
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "CameraConfiguration.h"
#include "PayloadConfiguration.h"
#include "enums.h"
void lmcp_pp_CameraConfiguration(CameraConfiguration* s) {
    printf("CameraConfiguration{");
    printf("Inherited from PayloadConfiguration:\n");
    lmcp_pp_PayloadConfiguration(&(s->super));
    printf("SupportedWavelengthBand: ");
    printf("%i", s->SupportedWavelengthBand);
    printf("\n");
    printf("FieldOfViewMode: ");
    printf("%i", s->FieldOfViewMode);
    printf("\n");
    printf("MinHorizontalFieldOfView: ");
    printf("%f",s->MinHorizontalFieldOfView);
    printf("\n");
    printf("MaxHorizontalFieldOfView: ");
    printf("%f",s->MaxHorizontalFieldOfView);
    printf("\n");
    printf("DiscreteHorizontalFieldOfViewList: ");
    printf("[");
    for (uint32_t index = 0; index < s->DiscreteHorizontalFieldOfViewList_ai.length; index++) {
        printf("%f",s->DiscreteHorizontalFieldOfViewList[index]);
        printf(",");
    }
    printf("\n");
    printf("VideoStreamHorizontalResolution: ");
    printf("%u",s->VideoStreamHorizontalResolution);
    printf("\n");
    printf("VideoStreamVerticalResolution: ");
    printf("%u",s->VideoStreamVerticalResolution);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_CameraConfiguration (CameraConfiguration* i) {
    size_t out = 0;
    out += lmcp_packsize_PayloadConfiguration(&(i->super));
    out += 4;
    out += 4;
    out += sizeof(float);
    out += sizeof(float);
    out += 2;
    for (uint32_t index = 0; index < i->DiscreteHorizontalFieldOfViewList_ai.length; index++) {
        out += sizeof(float);
    }
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    return out;
}
size_t lmcp_pack_CameraConfiguration_header(uint8_t* buf, CameraConfiguration* i) {
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
    outb += lmcp_pack_uint32_t(outb, 19);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_CameraConfiguration(CameraConfiguration* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_PayloadConfiguration(&(out->super), 0);
    if (out->DiscreteHorizontalFieldOfViewList != NULL) {
        free(out->DiscreteHorizontalFieldOfViewList);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_CameraConfiguration (CameraConfiguration** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(CameraConfiguration));
    ((lmcp_object*)(*i)) -> type = 19;
}
int lmcp_unpack_CameraConfiguration(uint8_t** inb, size_t *size_remain, CameraConfiguration* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    CameraConfiguration* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_PayloadConfiguration(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->SupportedWavelengthBand)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->FieldOfViewMode)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MinHorizontalFieldOfView)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaxHorizontalFieldOfView)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->DiscreteHorizontalFieldOfViewList = malloc(sizeof(float*) * tmp);
    if (out->DiscreteHorizontalFieldOfViewList==0) {
        return -1;
    }
    out->DiscreteHorizontalFieldOfViewList_ai.length = tmp;
    for (uint32_t index = 0; index < out->DiscreteHorizontalFieldOfViewList_ai.length; index++) {
        CHECK(lmcp_unpack_float(inb, size_remain, &out->DiscreteHorizontalFieldOfViewList[index]))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->VideoStreamHorizontalResolution)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->VideoStreamVerticalResolution)))
    return 0;
}
size_t lmcp_pack_CameraConfiguration(uint8_t* buf, CameraConfiguration* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_PayloadConfiguration(outb, &(i->super));
    outb += lmcp_pack_int32_t(outb, (int) i->SupportedWavelengthBand);
    outb += lmcp_pack_int32_t(outb, (int) i->FieldOfViewMode);
    outb += lmcp_pack_float(outb, i->MinHorizontalFieldOfView);
    outb += lmcp_pack_float(outb, i->MaxHorizontalFieldOfView);
    outb += lmcp_pack_uint16_t(outb, i->DiscreteHorizontalFieldOfViewList_ai.length);
    for (uint32_t index = 0; index < i->DiscreteHorizontalFieldOfViewList_ai.length; index++) {
        outb += lmcp_pack_float(outb, i->DiscreteHorizontalFieldOfViewList[index]);
    }
    outb += lmcp_pack_uint32_t(outb, i->VideoStreamHorizontalResolution);
    outb += lmcp_pack_uint32_t(outb, i->VideoStreamVerticalResolution);
    return (outb - buf);
}

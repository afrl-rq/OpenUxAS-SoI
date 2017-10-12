
#include "common/struct_defines.h"
#include "common/conv.h"
#include "CameraConfiguration.h"
#include "PayloadConfiguration.h"
#include "enums.h"
void lmcp_pp_CameraConfiguration(CameraConfiguration* s) {
    printf("CameraConfiguration{");
    printf("Inherited from PayloadConfiguration:\n");
    lmcp_pp_PayloadConfiguration(&(s->super));
    printf("supportedwavelengthband: ");
    printf("%i", s->supportedwavelengthband);
    printf("\n");
    printf("fieldofviewmode: ");
    printf("%i", s->fieldofviewmode);
    printf("\n");
    printf("minhorizontalfieldofview: ");
    printf("%u",s->minhorizontalfieldofview);
    printf("\n");
    printf("maxhorizontalfieldofview: ");
    printf("%u",s->maxhorizontalfieldofview);
    printf("\n");
    printf("discretehorizontalfieldofviewlist: ");
    printf("[");
    for (uint32_t index = 0; index < s->discretehorizontalfieldofviewlist_ai.length; index++) {
        printf("%u",s->discretehorizontalfieldofviewlist[index]);
        printf(",");
    }
    printf("\n");
    printf("videostreamhorizontalresolution: ");
    printf("%u",s->videostreamhorizontalresolution);
    printf("\n");
    printf("videostreamverticalresolution: ");
    printf("%u",s->videostreamverticalresolution);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_CameraConfiguration (CameraConfiguration* i) {
    size_t out = 0;
    out += lmcp_packsize_PayloadConfiguration(&(i->super));
    out += 4;
    out += 4;
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += 2;
    for (uint32_t index = 0; index < i->discretehorizontalfieldofviewlist_ai.length; index++) {
        out += sizeof(uint32_t);
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
    if (out->discretehorizontalfieldofviewlist != NULL) {
        free(out->discretehorizontalfieldofviewlist);
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
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->supportedwavelengthband)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->fieldofviewmode)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->minhorizontalfieldofview)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maxhorizontalfieldofview)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->discretehorizontalfieldofviewlist = malloc(sizeof(uint32_t*) * tmp);
    if (out->discretehorizontalfieldofviewlist==0) {
        return -1;
    }
    out->discretehorizontalfieldofviewlist_ai.length = tmp;
    for (uint32_t index = 0; index < out->discretehorizontalfieldofviewlist_ai.length; index++) {
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &out->discretehorizontalfieldofviewlist[index]))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->videostreamhorizontalresolution)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->videostreamverticalresolution)))
    return 0;
}
size_t lmcp_pack_CameraConfiguration(uint8_t* buf, CameraConfiguration* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_PayloadConfiguration(outb, &(i->super));
    outb += lmcp_pack_int32_t(outb, (int) i->supportedwavelengthband);
    outb += lmcp_pack_int32_t(outb, (int) i->fieldofviewmode);
    outb += lmcp_pack_uint32_t(outb, i->minhorizontalfieldofview);
    outb += lmcp_pack_uint32_t(outb, i->maxhorizontalfieldofview);
    outb += lmcp_pack_uint16_t(outb, i->discretehorizontalfieldofviewlist_ai.length);
    for (uint32_t index = 0; index < i->discretehorizontalfieldofviewlist_ai.length; index++) {
        outb += lmcp_pack_uint32_t(outb, i->discretehorizontalfieldofviewlist[index]);
    }
    outb += lmcp_pack_uint32_t(outb, i->videostreamhorizontalresolution);
    outb += lmcp_pack_uint32_t(outb, i->videostreamverticalresolution);
    return (outb - buf);
}

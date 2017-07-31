
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VideoStreamConfiguration.h"
#include "PayloadConfiguration.h"
void lmcp_pp_VideoStreamConfiguration(VideoStreamConfiguration* s) {
    printf("VideoStreamConfiguration{");
    printf("Inherited from PayloadConfiguration:\n");
    lmcp_pp_PayloadConfiguration(&(s->super));
    printf("AvailableSensorList: ");
    printf("[");
    for (uint32_t index = 0; index < s->AvailableSensorList_ai.length; index++) {
        printf("%lld",s->AvailableSensorList[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_VideoStreamConfiguration (VideoStreamConfiguration* i) {
    size_t out = 0;
    out += lmcp_packsize_PayloadConfiguration(&(i->super));
    out += 2;
    for (uint32_t index = 0; index < i->AvailableSensorList_ai.length; index++) {
        out += sizeof(int64_t);
    }
    return out;
}
size_t lmcp_pack_VideoStreamConfiguration_header(uint8_t* buf, VideoStreamConfiguration* i) {
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
    outb += lmcp_pack_uint32_t(outb, 49);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_VideoStreamConfiguration(VideoStreamConfiguration* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_PayloadConfiguration(&(out->super), 0);
    if (out->AvailableSensorList != NULL) {
        free(out->AvailableSensorList);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_VideoStreamConfiguration (VideoStreamConfiguration** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(VideoStreamConfiguration));
    ((lmcp_object*)(*i)) -> type = 49;
}
int lmcp_unpack_VideoStreamConfiguration(uint8_t** inb, size_t *size_remain, VideoStreamConfiguration* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    VideoStreamConfiguration* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_PayloadConfiguration(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->AvailableSensorList = malloc(sizeof(int64_t*) * tmp);
    if (out->AvailableSensorList==0) {
        return -1;
    }
    out->AvailableSensorList_ai.length = tmp;
    for (uint32_t index = 0; index < out->AvailableSensorList_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->AvailableSensorList[index]))
    }
    return 0;
}
size_t lmcp_pack_VideoStreamConfiguration(uint8_t* buf, VideoStreamConfiguration* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_PayloadConfiguration(outb, &(i->super));
    outb += lmcp_pack_uint16_t(outb, i->AvailableSensorList_ai.length);
    for (uint32_t index = 0; index < i->AvailableSensorList_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->AvailableSensorList[index]);
    }
    return (outb - buf);
}


#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VideoStreamAction.h"
#include "VehicleAction.h"
void lmcp_pp_VideoStreamAction(VideoStreamAction* s) {
    printf("VideoStreamAction{");
    printf("Inherited from VehicleAction:\n");
    lmcp_pp_VehicleAction(&(s->super));
    printf("VideoStreamID: ");
    printf("%i",s->VideoStreamID);
    printf("\n");
    printf("ActiveSensor: ");
    printf("%i",s->ActiveSensor);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_VideoStreamAction (VideoStreamAction* i) {
    size_t out = 0;
    out += lmcp_packsize_VehicleAction(&(i->super));
    out += sizeof(int32_t);
    out += sizeof(int32_t);
    return out;
}
size_t lmcp_pack_VideoStreamAction_header(uint8_t* buf, VideoStreamAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 48);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_VideoStreamAction(VideoStreamAction* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_VehicleAction(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_VideoStreamAction (VideoStreamAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(VideoStreamAction));
    ((lmcp_object*)(*i)) -> type = 48;
}
int lmcp_unpack_VideoStreamAction(uint8_t** inb, size_t *size_remain, VideoStreamAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    VideoStreamAction* out = outp;
    CHECK(lmcp_unpack_VehicleAction(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, &(out->VideoStreamID)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, &(out->ActiveSensor)))
    return 0;
}
size_t lmcp_pack_VideoStreamAction(uint8_t* buf, VideoStreamAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_VehicleAction(outb, &(i->super));
    outb += lmcp_pack_int32_t(outb, i->VideoStreamID);
    outb += lmcp_pack_int32_t(outb, i->ActiveSensor);
    return (outb - buf);
}


#include "common/struct_defines.h"
#include "common/conv.h"
#include "GimbalScanAction.h"
#include "PayloadAction.h"
void lmcp_pp_GimbalScanAction(GimbalScanAction* s) {
    printf("GimbalScanAction{");
    printf("Inherited from PayloadAction:\n");
    lmcp_pp_PayloadAction(&(s->super));
    printf("azimuthslewrate: ");
    printf("%u",s->azimuthslewrate);
    printf("\n");
    printf("elevationslewrate: ");
    printf("%u",s->elevationslewrate);
    printf("\n");
    printf("startazimuth: ");
    printf("%u",s->startazimuth);
    printf("\n");
    printf("endazimuth: ");
    printf("%u",s->endazimuth);
    printf("\n");
    printf("startelevation: ");
    printf("%u",s->startelevation);
    printf("\n");
    printf("endelevation: ");
    printf("%u",s->endelevation);
    printf("\n");
    printf("cycles: ");
    printf("%u",s->cycles);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_GimbalScanAction (GimbalScanAction* i) {
    size_t out = 0;
    out += lmcp_packsize_PayloadAction(&(i->super));
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    return out;
}
size_t lmcp_pack_GimbalScanAction_header(uint8_t* buf, GimbalScanAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 25);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_GimbalScanAction(GimbalScanAction* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_PayloadAction(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_GimbalScanAction (GimbalScanAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(GimbalScanAction));
    ((lmcp_object*)(*i)) -> type = 25;
}
int lmcp_unpack_GimbalScanAction(uint8_t** inb, size_t *size_remain, GimbalScanAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    GimbalScanAction* out = outp;
    CHECK(lmcp_unpack_PayloadAction(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->azimuthslewrate)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->elevationslewrate)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->startazimuth)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->endazimuth)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->startelevation)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->endelevation)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->cycles)))
    return 0;
}
size_t lmcp_pack_GimbalScanAction(uint8_t* buf, GimbalScanAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_PayloadAction(outb, &(i->super));
    outb += lmcp_pack_uint32_t(outb, i->azimuthslewrate);
    outb += lmcp_pack_uint32_t(outb, i->elevationslewrate);
    outb += lmcp_pack_uint32_t(outb, i->startazimuth);
    outb += lmcp_pack_uint32_t(outb, i->endazimuth);
    outb += lmcp_pack_uint32_t(outb, i->startelevation);
    outb += lmcp_pack_uint32_t(outb, i->endelevation);
    outb += lmcp_pack_uint32_t(outb, i->cycles);
    return (outb - buf);
}

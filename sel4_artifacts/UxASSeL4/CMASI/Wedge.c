
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Wedge.h"
void lmcp_pp_Wedge(Wedge* s) {
    printf("Wedge{");
    printf("AzimuthCenterline: ");
    printf("%f",s->AzimuthCenterline);
    printf("\n");
    printf("VerticalCenterline: ");
    printf("%f",s->VerticalCenterline);
    printf("\n");
    printf("AzimuthExtent: ");
    printf("%f",s->AzimuthExtent);
    printf("\n");
    printf("VerticalExtent: ");
    printf("%f",s->VerticalExtent);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_Wedge (Wedge* i) {
    size_t out = 0;
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    return out;
}
size_t lmcp_pack_Wedge_header(uint8_t* buf, Wedge* i) {
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
    outb += lmcp_pack_uint32_t(outb, 16);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_Wedge(Wedge* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_Wedge (Wedge** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(Wedge));
    ((lmcp_object*)(*i)) -> type = 16;
}
int lmcp_unpack_Wedge(uint8_t** inb, size_t *size_remain, Wedge* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    Wedge* out = outp;
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->AzimuthCenterline)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->VerticalCenterline)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->AzimuthExtent)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->VerticalExtent)))
    return 0;
}
size_t lmcp_pack_Wedge(uint8_t* buf, Wedge* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_float(outb, i->AzimuthCenterline);
    outb += lmcp_pack_float(outb, i->VerticalCenterline);
    outb += lmcp_pack_float(outb, i->AzimuthExtent);
    outb += lmcp_pack_float(outb, i->VerticalExtent);
    return (outb - buf);
}


#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "OperatingRegion.h"
void lmcp_pp_OperatingRegion(OperatingRegion* s) {
    printf("OperatingRegion{");
    printf("ID: ");
    printf("%lld",s->ID);
    printf("\n");
    printf("KeepInAreas: ");
    printf("[");
    for (uint32_t index = 0; index < s->KeepInAreas_ai.length; index++) {
        printf("%lld",s->KeepInAreas[index]);
        printf(",");
    }
    printf("\n");
    printf("KeepOutAreas: ");
    printf("[");
    for (uint32_t index = 0; index < s->KeepOutAreas_ai.length; index++) {
        printf("%lld",s->KeepOutAreas[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_OperatingRegion (OperatingRegion* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->KeepInAreas_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += 2;
    for (uint32_t index = 0; index < i->KeepOutAreas_ai.length; index++) {
        out += sizeof(int64_t);
    }
    return out;
}
size_t lmcp_pack_OperatingRegion_header(uint8_t* buf, OperatingRegion* i) {
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
    outb += lmcp_pack_uint32_t(outb, 39);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_OperatingRegion(OperatingRegion* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->KeepInAreas != NULL) {
        free(out->KeepInAreas);
    }
    if (out->KeepOutAreas != NULL) {
        free(out->KeepOutAreas);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_OperatingRegion (OperatingRegion** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(OperatingRegion));
    ((lmcp_object*)(*i)) -> type = 39;
}
int lmcp_unpack_OperatingRegion(uint8_t** inb, size_t *size_remain, OperatingRegion* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    OperatingRegion* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->ID)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->KeepInAreas = malloc(sizeof(int64_t*) * tmp);
    if (out->KeepInAreas==0) {
        return -1;
    }
    out->KeepInAreas_ai.length = tmp;
    for (uint32_t index = 0; index < out->KeepInAreas_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->KeepInAreas[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->KeepOutAreas = malloc(sizeof(int64_t*) * tmp);
    if (out->KeepOutAreas==0) {
        return -1;
    }
    out->KeepOutAreas_ai.length = tmp;
    for (uint32_t index = 0; index < out->KeepOutAreas_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->KeepOutAreas[index]))
    }
    return 0;
}
size_t lmcp_pack_OperatingRegion(uint8_t* buf, OperatingRegion* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->ID);
    outb += lmcp_pack_uint16_t(outb, i->KeepInAreas_ai.length);
    for (uint32_t index = 0; index < i->KeepInAreas_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->KeepInAreas[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->KeepOutAreas_ai.length);
    for (uint32_t index = 0; index < i->KeepOutAreas_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->KeepOutAreas[index]);
    }
    return (outb - buf);
}

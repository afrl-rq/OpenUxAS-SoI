
#include "common/struct_defines.h"
#include "common/conv.h"
#include "OperatingRegion.h"
void lmcp_pp_OperatingRegion(OperatingRegion* s) {
    printf("OperatingRegion{");
    printf("id: ");
    printf("%lld",s->id);
    printf("\n");
    printf("keepinareas: ");
    printf("[");
    for (uint32_t index = 0; index < s->keepinareas_ai.length; index++) {
        printf("%lld",s->keepinareas[index]);
        printf(",");
    }
    printf("\n");
    printf("keepoutareas: ");
    printf("[");
    for (uint32_t index = 0; index < s->keepoutareas_ai.length; index++) {
        printf("%lld",s->keepoutareas[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_OperatingRegion (OperatingRegion* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->keepinareas_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += 2;
    for (uint32_t index = 0; index < i->keepoutareas_ai.length; index++) {
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
    if (out->keepinareas != NULL) {
        free(out->keepinareas);
    }
    if (out->keepoutareas != NULL) {
        free(out->keepoutareas);
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
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->id)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->keepinareas = malloc(sizeof(int64_t*) * tmp);
    if (out->keepinareas==0) {
        return -1;
    }
    out->keepinareas_ai.length = tmp;
    for (uint32_t index = 0; index < out->keepinareas_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->keepinareas[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->keepoutareas = malloc(sizeof(int64_t*) * tmp);
    if (out->keepoutareas==0) {
        return -1;
    }
    out->keepoutareas_ai.length = tmp;
    for (uint32_t index = 0; index < out->keepoutareas_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->keepoutareas[index]))
    }
    return 0;
}
size_t lmcp_pack_OperatingRegion(uint8_t* buf, OperatingRegion* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->id);
    outb += lmcp_pack_uint16_t(outb, i->keepinareas_ai.length);
    for (uint32_t index = 0; index < i->keepinareas_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->keepinareas[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->keepoutareas_ai.length);
    for (uint32_t index = 0; index < i->keepoutareas_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->keepoutareas[index]);
    }
    return (outb - buf);
}

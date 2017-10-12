
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AbstractZone.h"
#include "enums.h"
#include "AbstractGeometry.h"
void lmcp_pp_AbstractZone(AbstractZone* s) {
    printf("AbstractZone{");
    printf("zoneid: ");
    printf("%lld",s->zoneid);
    printf("\n");
    printf("minaltitude: ");
    printf("%u",s->minaltitude);
    printf("\n");
    printf("minaltitudetype: ");
    printf("%i", s->minaltitudetype);
    printf("\n");
    printf("maxaltitude: ");
    printf("%u",s->maxaltitude);
    printf("\n");
    printf("maxaltitudetype: ");
    printf("%i", s->maxaltitudetype);
    printf("\n");
    printf("affectedaircraft: ");
    printf("[");
    for (uint32_t index = 0; index < s->affectedaircraft_ai.length; index++) {
        printf("%lld",s->affectedaircraft[index]);
        printf(",");
    }
    printf("\n");
    printf("starttime: ");
    printf("%lld",s->starttime);
    printf("\n");
    printf("endtime: ");
    printf("%lld",s->endtime);
    printf("\n");
    printf("padding: ");
    printf("%u",s->padding);
    printf("\n");
    printf("label: ");
    printf("[");
    for (uint32_t index = 0; index < s->label_ai.length; index++) {
        printf("%c",s->label[index]);
        printf(",");
    }
    printf("\n");
    printf("boundary: ");
    lmcp_pp_AbstractGeometry((s->boundary));
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_AbstractZone (AbstractZone* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += sizeof(uint32_t);
    out += 4;
    out += sizeof(uint32_t);
    out += 4;
    out += 2;
    for (uint32_t index = 0; index < i->affectedaircraft_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += sizeof(int64_t);
    out += sizeof(int64_t);
    out += sizeof(uint32_t);
    out += 2;
    for (uint32_t index = 0; index < i->label_ai.length; index++) {
        out += sizeof(char);
    }
    if (i->boundary==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_AbstractGeometry(i->boundary);
    }
    return out;
}
size_t lmcp_pack_AbstractZone_header(uint8_t* buf, AbstractZone* i) {
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
    outb += lmcp_pack_uint32_t(outb, 10);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_AbstractZone(AbstractZone* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->affectedaircraft != NULL) {
        free(out->affectedaircraft);
    }
    if (out->label != NULL) {
        free(out->label);
    }
    if (out->boundary != NULL) {
        lmcp_free_AbstractGeometry(out->boundary, 1);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_AbstractZone (AbstractZone** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(AbstractZone));
    ((lmcp_object*)(*i)) -> type = 10;
}
int lmcp_unpack_AbstractZone(uint8_t** inb, size_t *size_remain, AbstractZone* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    AbstractZone* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->zoneid)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->minaltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->minaltitudetype)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maxaltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->maxaltitudetype)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->affectedaircraft = malloc(sizeof(int64_t*) * tmp);
    if (out->affectedaircraft==0) {
        return -1;
    }
    out->affectedaircraft_ai.length = tmp;
    for (uint32_t index = 0; index < out->affectedaircraft_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->affectedaircraft[index]))
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->starttime)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->endtime)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->padding)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->label = malloc(sizeof(char*) * tmp);
    if (out->label==0) {
        return -1;
    }
    out->label_ai.length = tmp;
    for (uint32_t index = 0; index < out->label_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->label[index]))
    }
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->boundary = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_AbstractGeometry(&(out->boundary));
        CHECK(lmcp_unpack_AbstractGeometry(inb, size_remain, (out->boundary)))
    }
    return 0;
}
size_t lmcp_pack_AbstractZone(uint8_t* buf, AbstractZone* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->zoneid);
    outb += lmcp_pack_uint32_t(outb, i->minaltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->minaltitudetype);
    outb += lmcp_pack_uint32_t(outb, i->maxaltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->maxaltitudetype);
    outb += lmcp_pack_uint16_t(outb, i->affectedaircraft_ai.length);
    for (uint32_t index = 0; index < i->affectedaircraft_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->affectedaircraft[index]);
    }
    outb += lmcp_pack_int64_t(outb, i->starttime);
    outb += lmcp_pack_int64_t(outb, i->endtime);
    outb += lmcp_pack_uint32_t(outb, i->padding);
    outb += lmcp_pack_uint16_t(outb, i->label_ai.length);
    for (uint32_t index = 0; index < i->label_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->label[index]);
    }
    if (i->boundary==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 1);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_AbstractGeometry(outb, i->boundary);
    }
    return (outb - buf);
}

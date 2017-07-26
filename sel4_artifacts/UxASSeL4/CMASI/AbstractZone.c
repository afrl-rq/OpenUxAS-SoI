
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AbstractZone.h"
#include "enums.h"
#include "AbstractGeometry.h"
void lmcp_pp_AbstractZone(AbstractZone* s) {
    printf("AbstractZone{");
    printf("ZoneID: ");
    printf("%lld",s->ZoneID);
    printf("\n");
    printf("MinAltitude: ");
    printf("%f",s->MinAltitude);
    printf("\n");
    printf("MinAltitudeType: ");
    printf("%i", s->MinAltitudeType);
    printf("\n");
    printf("MaxAltitude: ");
    printf("%f",s->MaxAltitude);
    printf("\n");
    printf("MaxAltitudeType: ");
    printf("%i", s->MaxAltitudeType);
    printf("\n");
    printf("AffectedAircraft: ");
    printf("[");
    for (uint32_t index = 0; index < s->AffectedAircraft_ai.length; index++) {
        printf("%lld",s->AffectedAircraft[index]);
        printf(",");
    }
    printf("\n");
    printf("StartTime: ");
    printf("%lld",s->StartTime);
    printf("\n");
    printf("EndTime: ");
    printf("%lld",s->EndTime);
    printf("\n");
    printf("Padding: ");
    printf("%f",s->Padding);
    printf("\n");
    printf("Label: ");
    printf("[");
    for (uint32_t index = 0; index < s->Label_ai.length; index++) {
        printf("%c",s->Label[index]);
        printf(",");
    }
    printf("\n");
    printf("Boundary: ");
    lmcp_pp_AbstractGeometry((s->Boundary));
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_AbstractZone (AbstractZone* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += sizeof(float);
    out += 4;
    out += sizeof(float);
    out += 4;
    out += 2;
    for (uint32_t index = 0; index < i->AffectedAircraft_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += sizeof(int64_t);
    out += sizeof(int64_t);
    out += sizeof(float);
    out += 2;
    for (uint32_t index = 0; index < i->Label_ai.length; index++) {
        out += sizeof(char);
    }
    if (i->Boundary==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_AbstractGeometry(i->Boundary);
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
    if (out->AffectedAircraft != NULL) {
        free(out->AffectedAircraft);
    }
    if (out->Label != NULL) {
        free(out->Label);
    }
    if (out->Boundary != NULL) {
        lmcp_free_AbstractGeometry(out->Boundary, 1);
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
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->ZoneID)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MinAltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->MinAltitudeType)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaxAltitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->MaxAltitudeType)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->AffectedAircraft = malloc(sizeof(int64_t*) * tmp);
    if (out->AffectedAircraft==0) {
        return -1;
    }
    out->AffectedAircraft_ai.length = tmp;
    for (uint32_t index = 0; index < out->AffectedAircraft_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->AffectedAircraft[index]))
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->StartTime)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->EndTime)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Padding)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Label = malloc(sizeof(char*) * tmp);
    if (out->Label==0) {
        return -1;
    }
    out->Label_ai.length = tmp;
    for (uint32_t index = 0; index < out->Label_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->Label[index]))
    }
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->Boundary = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_AbstractGeometry(&(out->Boundary));
        CHECK(lmcp_unpack_AbstractGeometry(inb, size_remain, (out->Boundary)))
    }
    return 0;
}
size_t lmcp_pack_AbstractZone(uint8_t* buf, AbstractZone* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->ZoneID);
    outb += lmcp_pack_float(outb, i->MinAltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->MinAltitudeType);
    outb += lmcp_pack_float(outb, i->MaxAltitude);
    outb += lmcp_pack_int32_t(outb, (int) i->MaxAltitudeType);
    outb += lmcp_pack_uint16_t(outb, i->AffectedAircraft_ai.length);
    for (uint32_t index = 0; index < i->AffectedAircraft_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->AffectedAircraft[index]);
    }
    outb += lmcp_pack_int64_t(outb, i->StartTime);
    outb += lmcp_pack_int64_t(outb, i->EndTime);
    outb += lmcp_pack_float(outb, i->Padding);
    outb += lmcp_pack_uint16_t(outb, i->Label_ai.length);
    for (uint32_t index = 0; index < i->Label_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->Label[index]);
    }
    if (i->Boundary==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 1);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_AbstractGeometry(outb, i->Boundary);
    }
    return (outb - buf);
}

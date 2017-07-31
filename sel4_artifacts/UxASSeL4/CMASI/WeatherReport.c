
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "WeatherReport.h"
#include "AbstractZone.h"
void lmcp_pp_WeatherReport(WeatherReport* s) {
    printf("WeatherReport{");
    printf("Area: ");
    lmcp_pp_AbstractZone((s->Area));
    printf("\n");
    printf("WindSpeed: ");
    printf("%f",s->WindSpeed);
    printf("\n");
    printf("WindDirection: ");
    printf("%f",s->WindDirection);
    printf("\n");
    printf("Visibility: ");
    printf("%f",s->Visibility);
    printf("\n");
    printf("CloudCeiling: ");
    printf("%f",s->CloudCeiling);
    printf("\n");
    printf("CloudCoverage: ");
    printf("%f",s->CloudCoverage);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_WeatherReport (WeatherReport* i) {
    size_t out = 0;
    if (i->Area==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_AbstractZone(i->Area);
    }
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    return out;
}
size_t lmcp_pack_WeatherReport_header(uint8_t* buf, WeatherReport* i) {
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
    outb += lmcp_pack_uint32_t(outb, 55);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_WeatherReport(WeatherReport* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->Area != NULL) {
        lmcp_free_AbstractZone(out->Area, 1);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_WeatherReport (WeatherReport** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(WeatherReport));
    ((lmcp_object*)(*i)) -> type = 55;
}
int lmcp_unpack_WeatherReport(uint8_t** inb, size_t *size_remain, WeatherReport* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    WeatherReport* out = outp;
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->Area = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_AbstractZone(&(out->Area));
        CHECK(lmcp_unpack_AbstractZone(inb, size_remain, (out->Area)))
    }
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->WindSpeed)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->WindDirection)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Visibility)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->CloudCeiling)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->CloudCoverage)))
    return 0;
}
size_t lmcp_pack_WeatherReport(uint8_t* buf, WeatherReport* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    if (i->Area==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 10);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_AbstractZone(outb, i->Area);
    }
    outb += lmcp_pack_float(outb, i->WindSpeed);
    outb += lmcp_pack_float(outb, i->WindDirection);
    outb += lmcp_pack_float(outb, i->Visibility);
    outb += lmcp_pack_float(outb, i->CloudCeiling);
    outb += lmcp_pack_float(outb, i->CloudCoverage);
    return (outb - buf);
}

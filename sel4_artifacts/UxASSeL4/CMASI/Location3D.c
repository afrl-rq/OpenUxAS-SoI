
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Location3D.h"
#include "enums.h"
void lmcp_pp_Location3D(Location3D* s) {
    printf("Location3D{");
    printf("Latitude: ");
    printf("%f",s->Latitude);
    printf("\n");
    printf("Longitude: ");
    printf("%f",s->Longitude);
    printf("\n");
    printf("Altitude: ");
    printf("%f",s->Altitude);
    printf("\n");
    printf("AltitudeType: ");
    printf("%i", s->AltitudeType);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_Location3D (Location3D* i) {
    size_t out = 0;
    out += sizeof(double);
    out += sizeof(double);
    out += sizeof(float);
    out += 4;
    return out;
}
size_t lmcp_pack_Location3D_header(uint8_t* buf, Location3D* i) {
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
    outb += lmcp_pack_uint32_t(outb, 3);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_Location3D(Location3D* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_Location3D (Location3D** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(Location3D));
    ((lmcp_object*)(*i)) -> type = 3;
}
int lmcp_unpack_Location3D(uint8_t** inb, size_t *size_remain, Location3D* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    Location3D* out = outp;
    CHECK(lmcp_unpack_double(inb, size_remain, &(out->Latitude)))
    CHECK(lmcp_unpack_double(inb, size_remain, &(out->Longitude)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Altitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->AltitudeType)))
    return 0;
}
size_t lmcp_pack_Location3D(uint8_t* buf, Location3D* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_double(outb, i->Latitude);
    outb += lmcp_pack_double(outb, i->Longitude);
    outb += lmcp_pack_float(outb, i->Altitude);
    outb += lmcp_pack_int32_t(outb, (int) i->AltitudeType);
    return (outb - buf);
}

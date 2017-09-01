
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Location3D.h"
#include "enums.h"
void lmcp_pp_Location3D(Location3D* s) {
    printf("Location3D{");
    printf("latitude: ");
    printf("%llu",s->latitude);
    printf("\n");
    printf("longitude: ");
    printf("%llu",s->longitude);
    printf("\n");
    printf("altitude: ");
    printf("%u",s->altitude);
    printf("\n");
    printf("altitudetype: ");
    printf("%i", s->altitudetype);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_Location3D (Location3D* i) {
    size_t out = 0;
    out += sizeof(uint64_t);
    out += sizeof(uint64_t);
    out += sizeof(uint32_t);
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
    CHECK(lmcp_unpack_uint64_t(inb, size_remain, &(out->latitude)))
    CHECK(lmcp_unpack_uint64_t(inb, size_remain, &(out->longitude)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->altitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->altitudetype)))
    return 0;
}
size_t lmcp_pack_Location3D(uint8_t* buf, Location3D* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint64_t(outb, i->latitude);
    outb += lmcp_pack_uint64_t(outb, i->longitude);
    outb += lmcp_pack_uint32_t(outb, i->altitude);
    outb += lmcp_pack_int32_t(outb, (int) i->altitudetype);
    return (outb - buf);
}

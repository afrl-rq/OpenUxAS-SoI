
#include "common/struct_defines.h"
#include "common/conv.h"
#include "FlightProfile.h"
void lmcp_pp_FlightProfile(FlightProfile* s) {
    printf("FlightProfile{");
    printf("name: ");
    printf("[");
    for (uint32_t index = 0; index < s->name_ai.length; index++) {
        printf("%c",s->name[index]);
        printf(",");
    }
    printf("\n");
    printf("airspeed: ");
    printf("%u",s->airspeed);
    printf("\n");
    printf("pitchangle: ");
    printf("%u",s->pitchangle);
    printf("\n");
    printf("verticalspeed: ");
    printf("%u",s->verticalspeed);
    printf("\n");
    printf("maxbankangle: ");
    printf("%u",s->maxbankangle);
    printf("\n");
    printf("energyrate: ");
    printf("%u",s->energyrate);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_FlightProfile (FlightProfile* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->name_ai.length; index++) {
        out += sizeof(char);
    }
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    return out;
}
size_t lmcp_pack_FlightProfile_header(uint8_t* buf, FlightProfile* i) {
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
    outb += lmcp_pack_uint32_t(outb, 12);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_FlightProfile(FlightProfile* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->name != NULL) {
        free(out->name);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_FlightProfile (FlightProfile** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(FlightProfile));
    ((lmcp_object*)(*i)) -> type = 12;
}
int lmcp_unpack_FlightProfile(uint8_t** inb, size_t *size_remain, FlightProfile* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    FlightProfile* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->name = malloc(sizeof(char*) * tmp);
    if (out->name==0) {
        return -1;
    }
    out->name_ai.length = tmp;
    for (uint32_t index = 0; index < out->name_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->name[index]))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->airspeed)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->pitchangle)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->verticalspeed)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maxbankangle)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->energyrate)))
    return 0;
}
size_t lmcp_pack_FlightProfile(uint8_t* buf, FlightProfile* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->name_ai.length);
    for (uint32_t index = 0; index < i->name_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->name[index]);
    }
    outb += lmcp_pack_uint32_t(outb, i->airspeed);
    outb += lmcp_pack_uint32_t(outb, i->pitchangle);
    outb += lmcp_pack_uint32_t(outb, i->verticalspeed);
    outb += lmcp_pack_uint32_t(outb, i->maxbankangle);
    outb += lmcp_pack_uint32_t(outb, i->energyrate);
    return (outb - buf);
}

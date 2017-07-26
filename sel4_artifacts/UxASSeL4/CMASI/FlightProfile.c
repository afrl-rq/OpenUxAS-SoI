
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "FlightProfile.h"
void lmcp_pp_FlightProfile(FlightProfile* s) {
    printf("FlightProfile{");
    printf("Name: ");
    printf("[");
    for (uint32_t index = 0; index < s->Name_ai.length; index++) {
        printf("%c",s->Name[index]);
        printf(",");
    }
    printf("\n");
    printf("Airspeed: ");
    printf("%f",s->Airspeed);
    printf("\n");
    printf("PitchAngle: ");
    printf("%f",s->PitchAngle);
    printf("\n");
    printf("VerticalSpeed: ");
    printf("%f",s->VerticalSpeed);
    printf("\n");
    printf("MaxBankAngle: ");
    printf("%f",s->MaxBankAngle);
    printf("\n");
    printf("EnergyRate: ");
    printf("%f",s->EnergyRate);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_FlightProfile (FlightProfile* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->Name_ai.length; index++) {
        out += sizeof(char);
    }
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
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
    if (out->Name != NULL) {
        free(out->Name);
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
    (out)->Name = malloc(sizeof(char*) * tmp);
    if (out->Name==0) {
        return -1;
    }
    out->Name_ai.length = tmp;
    for (uint32_t index = 0; index < out->Name_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->Name[index]))
    }
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Airspeed)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->PitchAngle)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->VerticalSpeed)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->MaxBankAngle)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->EnergyRate)))
    return 0;
}
size_t lmcp_pack_FlightProfile(uint8_t* buf, FlightProfile* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->Name_ai.length);
    for (uint32_t index = 0; index < i->Name_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->Name[index]);
    }
    outb += lmcp_pack_float(outb, i->Airspeed);
    outb += lmcp_pack_float(outb, i->PitchAngle);
    outb += lmcp_pack_float(outb, i->VerticalSpeed);
    outb += lmcp_pack_float(outb, i->MaxBankAngle);
    outb += lmcp_pack_float(outb, i->EnergyRate);
    return (outb - buf);
}

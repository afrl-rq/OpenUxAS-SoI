
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AirVehicleState.h"
#include "EntityState.h"
void lmcp_pp_AirVehicleState(AirVehicleState* s) {
    printf("AirVehicleState{");
    printf("Inherited from EntityState:\n");
    lmcp_pp_EntityState(&(s->super));
    printf("airspeed: ");
    printf("%u",s->airspeed);
    printf("\n");
    printf("verticalspeed: ");
    printf("%u",s->verticalspeed);
    printf("\n");
    printf("windspeed: ");
    printf("%u",s->windspeed);
    printf("\n");
    printf("winddirection: ");
    printf("%u",s->winddirection);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_AirVehicleState (AirVehicleState* i) {
    size_t out = 0;
    out += lmcp_packsize_EntityState(&(i->super));
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    return out;
}
size_t lmcp_pack_AirVehicleState_header(uint8_t* buf, AirVehicleState* i) {
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
    outb += lmcp_pack_uint32_t(outb, 15);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_AirVehicleState(AirVehicleState* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_EntityState(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_AirVehicleState (AirVehicleState** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(AirVehicleState));
    ((lmcp_object*)(*i)) -> type = 15;
}
int lmcp_unpack_AirVehicleState(uint8_t** inb, size_t *size_remain, AirVehicleState* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    AirVehicleState* out = outp;
    CHECK(lmcp_unpack_EntityState(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->airspeed)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->verticalspeed)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->windspeed)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->winddirection)))
    return 0;
}
size_t lmcp_pack_AirVehicleState(uint8_t* buf, AirVehicleState* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_EntityState(outb, &(i->super));
    outb += lmcp_pack_uint32_t(outb, i->airspeed);
    outb += lmcp_pack_uint32_t(outb, i->verticalspeed);
    outb += lmcp_pack_uint32_t(outb, i->windspeed);
    outb += lmcp_pack_uint32_t(outb, i->winddirection);
    return (outb - buf);
}

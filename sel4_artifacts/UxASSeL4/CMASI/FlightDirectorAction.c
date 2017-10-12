
#include "common/struct_defines.h"
#include "common/conv.h"
#include "FlightDirectorAction.h"
#include "NavigationAction.h"
#include "enums.h"
void lmcp_pp_FlightDirectorAction(FlightDirectorAction* s) {
    printf("FlightDirectorAction{");
    printf("Inherited from NavigationAction:\n");
    lmcp_pp_NavigationAction(&(s->super));
    printf("speed: ");
    printf("%u",s->speed);
    printf("\n");
    printf("speedtype: ");
    printf("%i", s->speedtype);
    printf("\n");
    printf("heading: ");
    printf("%u",s->heading);
    printf("\n");
    printf("altitude: ");
    printf("%u",s->altitude);
    printf("\n");
    printf("altitudetype: ");
    printf("%i", s->altitudetype);
    printf("\n");
    printf("climbrate: ");
    printf("%u",s->climbrate);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_FlightDirectorAction (FlightDirectorAction* i) {
    size_t out = 0;
    out += lmcp_packsize_NavigationAction(&(i->super));
    out += sizeof(uint32_t);
    out += 4;
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += 4;
    out += sizeof(uint32_t);
    return out;
}
size_t lmcp_pack_FlightDirectorAction_header(uint8_t* buf, FlightDirectorAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 54);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_FlightDirectorAction(FlightDirectorAction* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_NavigationAction(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_FlightDirectorAction (FlightDirectorAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(FlightDirectorAction));
    ((lmcp_object*)(*i)) -> type = 54;
}
int lmcp_unpack_FlightDirectorAction(uint8_t** inb, size_t *size_remain, FlightDirectorAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    FlightDirectorAction* out = outp;
    CHECK(lmcp_unpack_NavigationAction(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->speed)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->speedtype)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->heading)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->altitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->altitudetype)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->climbrate)))
    return 0;
}
size_t lmcp_pack_FlightDirectorAction(uint8_t* buf, FlightDirectorAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_NavigationAction(outb, &(i->super));
    outb += lmcp_pack_uint32_t(outb, i->speed);
    outb += lmcp_pack_int32_t(outb, (int) i->speedtype);
    outb += lmcp_pack_uint32_t(outb, i->heading);
    outb += lmcp_pack_uint32_t(outb, i->altitude);
    outb += lmcp_pack_int32_t(outb, (int) i->altitudetype);
    outb += lmcp_pack_uint32_t(outb, i->climbrate);
    return (outb - buf);
}

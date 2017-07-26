
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "FlightDirectorAction.h"
#include "NavigationAction.h"
#include "enums.h"
void lmcp_pp_FlightDirectorAction(FlightDirectorAction* s) {
    printf("FlightDirectorAction{");
    printf("Inherited from NavigationAction:\n");
    lmcp_pp_NavigationAction(&(s->super));
    printf("Speed: ");
    printf("%f",s->Speed);
    printf("\n");
    printf("SpeedType: ");
    printf("%i", s->SpeedType);
    printf("\n");
    printf("Heading: ");
    printf("%f",s->Heading);
    printf("\n");
    printf("Altitude: ");
    printf("%f",s->Altitude);
    printf("\n");
    printf("AltitudeType: ");
    printf("%i", s->AltitudeType);
    printf("\n");
    printf("ClimbRate: ");
    printf("%f",s->ClimbRate);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_FlightDirectorAction (FlightDirectorAction* i) {
    size_t out = 0;
    out += lmcp_packsize_NavigationAction(&(i->super));
    out += sizeof(float);
    out += 4;
    out += sizeof(float);
    out += sizeof(float);
    out += 4;
    out += sizeof(float);
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
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Speed)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->SpeedType)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Heading)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Altitude)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->AltitudeType)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->ClimbRate)))
    return 0;
}
size_t lmcp_pack_FlightDirectorAction(uint8_t* buf, FlightDirectorAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_NavigationAction(outb, &(i->super));
    outb += lmcp_pack_float(outb, i->Speed);
    outb += lmcp_pack_int32_t(outb, (int) i->SpeedType);
    outb += lmcp_pack_float(outb, i->Heading);
    outb += lmcp_pack_float(outb, i->Altitude);
    outb += lmcp_pack_int32_t(outb, (int) i->AltitudeType);
    outb += lmcp_pack_float(outb, i->ClimbRate);
    return (outb - buf);
}

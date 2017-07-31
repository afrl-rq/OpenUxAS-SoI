
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "GimbalScanAction.h"
#include "PayloadAction.h"
void lmcp_pp_GimbalScanAction(GimbalScanAction* s) {
    printf("GimbalScanAction{");
    printf("Inherited from PayloadAction:\n");
    lmcp_pp_PayloadAction(&(s->super));
    printf("AzimuthSlewRate: ");
    printf("%f",s->AzimuthSlewRate);
    printf("\n");
    printf("ElevationSlewRate: ");
    printf("%f",s->ElevationSlewRate);
    printf("\n");
    printf("StartAzimuth: ");
    printf("%f",s->StartAzimuth);
    printf("\n");
    printf("EndAzimuth: ");
    printf("%f",s->EndAzimuth);
    printf("\n");
    printf("StartElevation: ");
    printf("%f",s->StartElevation);
    printf("\n");
    printf("EndElevation: ");
    printf("%f",s->EndElevation);
    printf("\n");
    printf("Cycles: ");
    printf("%u",s->Cycles);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_GimbalScanAction (GimbalScanAction* i) {
    size_t out = 0;
    out += lmcp_packsize_PayloadAction(&(i->super));
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(uint32_t);
    return out;
}
size_t lmcp_pack_GimbalScanAction_header(uint8_t* buf, GimbalScanAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 25);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_GimbalScanAction(GimbalScanAction* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_PayloadAction(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_GimbalScanAction (GimbalScanAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(GimbalScanAction));
    ((lmcp_object*)(*i)) -> type = 25;
}
int lmcp_unpack_GimbalScanAction(uint8_t** inb, size_t *size_remain, GimbalScanAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    GimbalScanAction* out = outp;
    CHECK(lmcp_unpack_PayloadAction(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->AzimuthSlewRate)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->ElevationSlewRate)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->StartAzimuth)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->EndAzimuth)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->StartElevation)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->EndElevation)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->Cycles)))
    return 0;
}
size_t lmcp_pack_GimbalScanAction(uint8_t* buf, GimbalScanAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_PayloadAction(outb, &(i->super));
    outb += lmcp_pack_float(outb, i->AzimuthSlewRate);
    outb += lmcp_pack_float(outb, i->ElevationSlewRate);
    outb += lmcp_pack_float(outb, i->StartAzimuth);
    outb += lmcp_pack_float(outb, i->EndAzimuth);
    outb += lmcp_pack_float(outb, i->StartElevation);
    outb += lmcp_pack_float(outb, i->EndElevation);
    outb += lmcp_pack_uint32_t(outb, i->Cycles);
    return (outb - buf);
}

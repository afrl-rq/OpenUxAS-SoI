
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadAction.h"
#include "VehicleAction.h"
void lmcp_pp_PayloadAction(PayloadAction* s) {
    printf("PayloadAction{");
    printf("Inherited from VehicleAction:\n");
    lmcp_pp_VehicleAction(&(s->super));
    printf("PayloadID: ");
    printf("%lld",s->PayloadID);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_PayloadAction (PayloadAction* i) {
    size_t out = 0;
    out += lmcp_packsize_VehicleAction(&(i->super));
    out += sizeof(int64_t);
    return out;
}
size_t lmcp_pack_PayloadAction_header(uint8_t* buf, PayloadAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 4);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_PayloadAction(PayloadAction* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_VehicleAction(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_PayloadAction (PayloadAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(PayloadAction));
    ((lmcp_object*)(*i)) -> type = 4;
}
int lmcp_unpack_PayloadAction(uint8_t** inb, size_t *size_remain, PayloadAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    PayloadAction* out = outp;
    CHECK(lmcp_unpack_VehicleAction(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->PayloadID)))
    return 0;
}
size_t lmcp_pack_PayloadAction(uint8_t* buf, PayloadAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_VehicleAction(outb, &(i->super));
    outb += lmcp_pack_int64_t(outb, i->PayloadID);
    return (outb - buf);
}

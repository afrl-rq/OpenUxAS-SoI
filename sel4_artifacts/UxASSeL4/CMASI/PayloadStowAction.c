
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PayloadStowAction.h"
void lmcp_pp_PayloadStowAction(PayloadStowAction* s) {
    printf("PayloadStowAction{");
    printf("PayloadID: ");
    printf("%lld",s->PayloadID);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_PayloadStowAction (PayloadStowAction* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    return out;
}
size_t lmcp_pack_PayloadStowAction_header(uint8_t* buf, PayloadStowAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 60);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_PayloadStowAction(PayloadStowAction* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_PayloadStowAction (PayloadStowAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(PayloadStowAction));
    ((lmcp_object*)(*i)) -> type = 60;
}
int lmcp_unpack_PayloadStowAction(uint8_t** inb, size_t *size_remain, PayloadStowAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    PayloadStowAction* out = outp;
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->PayloadID)))
    return 0;
}
size_t lmcp_pack_PayloadStowAction(uint8_t* buf, PayloadStowAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->PayloadID);
    return (outb - buf);
}

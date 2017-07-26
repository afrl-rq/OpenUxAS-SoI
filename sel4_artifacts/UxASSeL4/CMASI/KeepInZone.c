
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "KeepInZone.h"
#include "AbstractZone.h"
void lmcp_pp_KeepInZone(KeepInZone* s) {
    printf("KeepInZone{");
    printf("Inherited from AbstractZone:\n");
    lmcp_pp_AbstractZone(&(s->super));
    printf("}");
}
size_t lmcp_packsize_KeepInZone (KeepInZone* i) {
    size_t out = 0;
    out += lmcp_packsize_AbstractZone(&(i->super));
    return out;
}
size_t lmcp_pack_KeepInZone_header(uint8_t* buf, KeepInZone* i) {
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
    outb += lmcp_pack_uint32_t(outb, 29);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_KeepInZone(KeepInZone* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_AbstractZone(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_KeepInZone (KeepInZone** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(KeepInZone));
    ((lmcp_object*)(*i)) -> type = 29;
}
int lmcp_unpack_KeepInZone(uint8_t** inb, size_t *size_remain, KeepInZone* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    KeepInZone* out = outp;
    CHECK(lmcp_unpack_AbstractZone(inb, size_remain, &(out->super)))
    return 0;
}
size_t lmcp_pack_KeepInZone(uint8_t* buf, KeepInZone* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_AbstractZone(outb, &(i->super));
    return (outb - buf);
}

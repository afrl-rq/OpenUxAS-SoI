
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "KeepOutZone.h"
#include "AbstractZone.h"
#include "enums.h"
void lmcp_pp_KeepOutZone(KeepOutZone* s) {
    printf("KeepOutZone{");
    printf("Inherited from AbstractZone:\n");
    lmcp_pp_AbstractZone(&(s->super));
    printf("ZoneType: ");
    printf("%i", s->ZoneType);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_KeepOutZone (KeepOutZone* i) {
    size_t out = 0;
    out += lmcp_packsize_AbstractZone(&(i->super));
    out += 4;
    return out;
}
size_t lmcp_pack_KeepOutZone_header(uint8_t* buf, KeepOutZone* i) {
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
    outb += lmcp_pack_uint32_t(outb, 30);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_KeepOutZone(KeepOutZone* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_AbstractZone(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_KeepOutZone (KeepOutZone** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(KeepOutZone));
    ((lmcp_object*)(*i)) -> type = 30;
}
int lmcp_unpack_KeepOutZone(uint8_t** inb, size_t *size_remain, KeepOutZone* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    KeepOutZone* out = outp;
    CHECK(lmcp_unpack_AbstractZone(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->ZoneType)))
    return 0;
}
size_t lmcp_pack_KeepOutZone(uint8_t* buf, KeepOutZone* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_AbstractZone(outb, &(i->super));
    outb += lmcp_pack_int32_t(outb, (int) i->ZoneType);
    return (outb - buf);
}

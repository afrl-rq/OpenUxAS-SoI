
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AbstractGeometry.h"
void lmcp_pp_AbstractGeometry(AbstractGeometry* s) {
    printf("AbstractGeometry{");
    printf("}");
}
size_t lmcp_packsize_AbstractGeometry (AbstractGeometry* i) {
    size_t out = 0;
    return out;
}
size_t lmcp_pack_AbstractGeometry_header(uint8_t* buf, AbstractGeometry* i) {
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
    outb += lmcp_pack_uint32_t(outb, 1);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_AbstractGeometry(AbstractGeometry* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_AbstractGeometry (AbstractGeometry** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(AbstractGeometry));
    ((lmcp_object*)(*i)) -> type = 1;
}
int lmcp_unpack_AbstractGeometry(uint8_t** inb, size_t *size_remain, AbstractGeometry* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    AbstractGeometry* out = outp;
    return 0;
}
size_t lmcp_pack_AbstractGeometry(uint8_t* buf, AbstractGeometry* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    return (outb - buf);
}

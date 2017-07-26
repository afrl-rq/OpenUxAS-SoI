
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "RemoveEntities.h"
void lmcp_pp_RemoveEntities(RemoveEntities* s) {
    printf("RemoveEntities{");
    printf("EntityList: ");
    printf("[");
    for (uint32_t index = 0; index < s->EntityList_ai.length; index++) {
        printf("%lld",s->EntityList[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_RemoveEntities (RemoveEntities* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->EntityList_ai.length; index++) {
        out += sizeof(int64_t);
    }
    return out;
}
size_t lmcp_pack_RemoveEntities_header(uint8_t* buf, RemoveEntities* i) {
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
    outb += lmcp_pack_uint32_t(outb, 53);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_RemoveEntities(RemoveEntities* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->EntityList != NULL) {
        free(out->EntityList);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_RemoveEntities (RemoveEntities** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(RemoveEntities));
    ((lmcp_object*)(*i)) -> type = 53;
}
int lmcp_unpack_RemoveEntities(uint8_t** inb, size_t *size_remain, RemoveEntities* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    RemoveEntities* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->EntityList = malloc(sizeof(int64_t*) * tmp);
    if (out->EntityList==0) {
        return -1;
    }
    out->EntityList_ai.length = tmp;
    for (uint32_t index = 0; index < out->EntityList_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->EntityList[index]))
    }
    return 0;
}
size_t lmcp_pack_RemoveEntities(uint8_t* buf, RemoveEntities* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->EntityList_ai.length);
    for (uint32_t index = 0; index < i->EntityList_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->EntityList[index]);
    }
    return (outb - buf);
}

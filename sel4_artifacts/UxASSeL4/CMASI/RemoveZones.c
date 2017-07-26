
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "RemoveZones.h"
void lmcp_pp_RemoveZones(RemoveZones* s) {
    printf("RemoveZones{");
    printf("ZoneList: ");
    printf("[");
    for (uint32_t index = 0; index < s->ZoneList_ai.length; index++) {
        printf("%lld",s->ZoneList[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_RemoveZones (RemoveZones* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->ZoneList_ai.length; index++) {
        out += sizeof(int64_t);
    }
    return out;
}
size_t lmcp_pack_RemoveZones_header(uint8_t* buf, RemoveZones* i) {
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
    outb += lmcp_pack_uint32_t(outb, 52);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_RemoveZones(RemoveZones* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->ZoneList != NULL) {
        free(out->ZoneList);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_RemoveZones (RemoveZones** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(RemoveZones));
    ((lmcp_object*)(*i)) -> type = 52;
}
int lmcp_unpack_RemoveZones(uint8_t** inb, size_t *size_remain, RemoveZones* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    RemoveZones* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->ZoneList = malloc(sizeof(int64_t*) * tmp);
    if (out->ZoneList==0) {
        return -1;
    }
    out->ZoneList_ai.length = tmp;
    for (uint32_t index = 0; index < out->ZoneList_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->ZoneList[index]))
    }
    return 0;
}
size_t lmcp_pack_RemoveZones(uint8_t* buf, RemoveZones* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->ZoneList_ai.length);
    for (uint32_t index = 0; index < i->ZoneList_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->ZoneList[index]);
    }
    return (outb - buf);
}


#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "RemoveTasks.h"
void lmcp_pp_RemoveTasks(RemoveTasks* s) {
    printf("RemoveTasks{");
    printf("TaskList: ");
    printf("[");
    for (uint32_t index = 0; index < s->TaskList_ai.length; index++) {
        printf("%lld",s->TaskList[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_RemoveTasks (RemoveTasks* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->TaskList_ai.length; index++) {
        out += sizeof(int64_t);
    }
    return out;
}
size_t lmcp_pack_RemoveTasks_header(uint8_t* buf, RemoveTasks* i) {
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
    outb += lmcp_pack_uint32_t(outb, 44);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_RemoveTasks(RemoveTasks* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->TaskList != NULL) {
        free(out->TaskList);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_RemoveTasks (RemoveTasks** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(RemoveTasks));
    ((lmcp_object*)(*i)) -> type = 44;
}
int lmcp_unpack_RemoveTasks(uint8_t** inb, size_t *size_remain, RemoveTasks* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    RemoveTasks* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->TaskList = malloc(sizeof(int64_t*) * tmp);
    if (out->TaskList==0) {
        return -1;
    }
    out->TaskList_ai.length = tmp;
    for (uint32_t index = 0; index < out->TaskList_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->TaskList[index]))
    }
    return 0;
}
size_t lmcp_pack_RemoveTasks(uint8_t* buf, RemoveTasks* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->TaskList_ai.length);
    for (uint32_t index = 0; index < i->TaskList_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->TaskList[index]);
    }
    return (outb - buf);
}

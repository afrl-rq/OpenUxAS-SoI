
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "VehicleAction.h"
void lmcp_pp_VehicleAction(VehicleAction* s) {
    printf("VehicleAction{");
    printf("AssociatedTaskList: ");
    printf("[");
    for (uint32_t index = 0; index < s->AssociatedTaskList_ai.length; index++) {
        printf("%lld",s->AssociatedTaskList[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_VehicleAction (VehicleAction* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->AssociatedTaskList_ai.length; index++) {
        out += sizeof(int64_t);
    }
    return out;
}
size_t lmcp_pack_VehicleAction_header(uint8_t* buf, VehicleAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 7);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_VehicleAction(VehicleAction* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->AssociatedTaskList != NULL) {
        free(out->AssociatedTaskList);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_VehicleAction (VehicleAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(VehicleAction));
    ((lmcp_object*)(*i)) -> type = 7;
}
int lmcp_unpack_VehicleAction(uint8_t** inb, size_t *size_remain, VehicleAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    VehicleAction* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->AssociatedTaskList = malloc(sizeof(int64_t*) * tmp);
    if (out->AssociatedTaskList==0) {
        return -1;
    }
    out->AssociatedTaskList_ai.length = tmp;
    for (uint32_t index = 0; index < out->AssociatedTaskList_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->AssociatedTaskList[index]))
    }
    return 0;
}
size_t lmcp_pack_VehicleAction(uint8_t* buf, VehicleAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->AssociatedTaskList_ai.length);
    for (uint32_t index = 0; index < i->AssociatedTaskList_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->AssociatedTaskList[index]);
    }
    return (outb - buf);
}

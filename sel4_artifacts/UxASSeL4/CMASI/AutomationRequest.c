
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AutomationRequest.h"
void lmcp_pp_AutomationRequest(AutomationRequest* s) {
    printf("AutomationRequest{");
    printf("EntityList: ");
    printf("[");
    for (uint32_t index = 0; index < s->EntityList_ai.length; index++) {
        printf("%lld",s->EntityList[index]);
        printf(",");
    }
    printf("\n");
    printf("TaskList: ");
    printf("[");
    for (uint32_t index = 0; index < s->TaskList_ai.length; index++) {
        printf("%lld",s->TaskList[index]);
        printf(",");
    }
    printf("\n");
    printf("TaskRelationships: ");
    printf("[");
    for (uint32_t index = 0; index < s->TaskRelationships_ai.length; index++) {
        printf("%c",s->TaskRelationships[index]);
        printf(",");
    }
    printf("\n");
    printf("OperatingRegion: ");
    printf("%lld",s->OperatingRegion);
    printf("\n");
    printf("RedoAllTasks: ");
    printf("%u",s->RedoAllTasks);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_AutomationRequest (AutomationRequest* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->EntityList_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += 2;
    for (uint32_t index = 0; index < i->TaskList_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += 2;
    for (uint32_t index = 0; index < i->TaskRelationships_ai.length; index++) {
        out += sizeof(char);
    }
    out += sizeof(int64_t);
    out += sizeof(uint8_t);
    return out;
}
size_t lmcp_pack_AutomationRequest_header(uint8_t* buf, AutomationRequest* i) {
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
    outb += lmcp_pack_uint32_t(outb, 40);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_AutomationRequest(AutomationRequest* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->EntityList != NULL) {
        free(out->EntityList);
    }
    if (out->TaskList != NULL) {
        free(out->TaskList);
    }
    if (out->TaskRelationships != NULL) {
        free(out->TaskRelationships);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_AutomationRequest (AutomationRequest** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(AutomationRequest));
    ((lmcp_object*)(*i)) -> type = 40;
}
int lmcp_unpack_AutomationRequest(uint8_t** inb, size_t *size_remain, AutomationRequest* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    AutomationRequest* out = outp;
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
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->TaskRelationships = malloc(sizeof(char*) * tmp);
    if (out->TaskRelationships==0) {
        return -1;
    }
    out->TaskRelationships_ai.length = tmp;
    for (uint32_t index = 0; index < out->TaskRelationships_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->TaskRelationships[index]))
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->OperatingRegion)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->RedoAllTasks)))
    return 0;
}
size_t lmcp_pack_AutomationRequest(uint8_t* buf, AutomationRequest* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->EntityList_ai.length);
    for (uint32_t index = 0; index < i->EntityList_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->EntityList[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->TaskList_ai.length);
    for (uint32_t index = 0; index < i->TaskList_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->TaskList[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->TaskRelationships_ai.length);
    for (uint32_t index = 0; index < i->TaskRelationships_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->TaskRelationships[index]);
    }
    outb += lmcp_pack_int64_t(outb, i->OperatingRegion);
    outb += lmcp_pack_uint8_t(outb, i->RedoAllTasks);
    return (outb - buf);
}

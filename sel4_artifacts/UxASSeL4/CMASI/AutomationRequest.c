
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AutomationRequest.h"
void lmcp_pp_AutomationRequest(AutomationRequest* s) {
    printf("AutomationRequest{");
    printf("entitylist: ");
    printf("[");
    for (uint32_t index = 0; index < s->entitylist_ai.length; index++) {
        printf("%lld",s->entitylist[index]);
        printf(",");
    }
    printf("\n");
    printf("tasklist: ");
    printf("[");
    for (uint32_t index = 0; index < s->tasklist_ai.length; index++) {
        printf("%lld",s->tasklist[index]);
        printf(",");
    }
    printf("\n");
    printf("taskrelationships: ");
    printf("[");
    for (uint32_t index = 0; index < s->taskrelationships_ai.length; index++) {
        printf("%c",s->taskrelationships[index]);
        printf(",");
    }
    printf("\n");
    printf("operatingregion: ");
    printf("%lld",s->operatingregion);
    printf("\n");
    printf("redoalltasks: ");
    printf("%u",s->redoalltasks);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_AutomationRequest (AutomationRequest* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->entitylist_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += 2;
    for (uint32_t index = 0; index < i->tasklist_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += 2;
    for (uint32_t index = 0; index < i->taskrelationships_ai.length; index++) {
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
    if (out->entitylist != NULL) {
        free(out->entitylist);
    }
    if (out->tasklist != NULL) {
        free(out->tasklist);
    }
    if (out->taskrelationships != NULL) {
        free(out->taskrelationships);
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
    (out)->entitylist = malloc(sizeof(int64_t*) * tmp);
    if (out->entitylist==0) {
        return -1;
    }
    out->entitylist_ai.length = tmp;
    for (uint32_t index = 0; index < out->entitylist_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->entitylist[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->tasklist = malloc(sizeof(int64_t*) * tmp);
    if (out->tasklist==0) {
        return -1;
    }
    out->tasklist_ai.length = tmp;
    for (uint32_t index = 0; index < out->tasklist_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->tasklist[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->taskrelationships = malloc(sizeof(char*) * tmp);
    if (out->taskrelationships==0) {
        return -1;
    }
    out->taskrelationships_ai.length = tmp;
    for (uint32_t index = 0; index < out->taskrelationships_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->taskrelationships[index]))
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->operatingregion)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->redoalltasks)))
    return 0;
}
size_t lmcp_pack_AutomationRequest(uint8_t* buf, AutomationRequest* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->entitylist_ai.length);
    for (uint32_t index = 0; index < i->entitylist_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->entitylist[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->tasklist_ai.length);
    for (uint32_t index = 0; index < i->tasklist_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->tasklist[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->taskrelationships_ai.length);
    for (uint32_t index = 0; index < i->taskrelationships_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->taskrelationships[index]);
    }
    outb += lmcp_pack_int64_t(outb, i->operatingregion);
    outb += lmcp_pack_uint8_t(outb, i->redoalltasks);
    return (outb - buf);
}

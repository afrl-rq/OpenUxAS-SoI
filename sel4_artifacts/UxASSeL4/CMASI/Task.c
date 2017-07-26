
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Task.h"
#include "KeyValuePair.h"
void lmcp_pp_Task(Task* s) {
    printf("Task{");
    printf("TaskID: ");
    printf("%lld",s->TaskID);
    printf("\n");
    printf("Label: ");
    printf("[");
    for (uint32_t index = 0; index < s->Label_ai.length; index++) {
        printf("%c",s->Label[index]);
        printf(",");
    }
    printf("\n");
    printf("EligibleEntities: ");
    printf("[");
    for (uint32_t index = 0; index < s->EligibleEntities_ai.length; index++) {
        printf("%lld",s->EligibleEntities[index]);
        printf(",");
    }
    printf("\n");
    printf("RevisitRate: ");
    printf("%f",s->RevisitRate);
    printf("\n");
    printf("Parameters: ");
    printf("[");
    for (uint32_t index = 0; index < s->Parameters_ai.length; index++) {
        lmcp_pp_KeyValuePair((s->Parameters[index]));
        printf(",");
    }
    printf("\n");
    printf("Priority: ");
    printf("%u",s->Priority);
    printf("\n");
    printf("Required: ");
    printf("%u",s->Required);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_Task (Task* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->Label_ai.length; index++) {
        out += sizeof(char);
    }
    out += 2;
    for (uint32_t index = 0; index < i->EligibleEntities_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += sizeof(float);
    out += 2;
    for (uint32_t index = 0; index < i->Parameters_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->Parameters[index]);
    }
    out += sizeof(uint8_t);
    out += sizeof(uint8_t);
    return out;
}
size_t lmcp_pack_Task_header(uint8_t* buf, Task* i) {
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
    outb += lmcp_pack_uint32_t(outb, 8);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_Task(Task* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->Label != NULL) {
        free(out->Label);
    }
    if (out->EligibleEntities != NULL) {
        free(out->EligibleEntities);
    }
    if (out->Parameters != NULL) {
        for (uint32_t index = 0; index < out->Parameters_ai.length; index++) {
            if (out->Parameters[index] != NULL) {
                lmcp_free_KeyValuePair(out->Parameters[index], 1);
            }
        }
        free(out->Parameters);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_Task (Task** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(Task));
    ((lmcp_object*)(*i)) -> type = 8;
}
int lmcp_unpack_Task(uint8_t** inb, size_t *size_remain, Task* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    Task* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->TaskID)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Label = malloc(sizeof(char*) * tmp);
    if (out->Label==0) {
        return -1;
    }
    out->Label_ai.length = tmp;
    for (uint32_t index = 0; index < out->Label_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->Label[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->EligibleEntities = malloc(sizeof(int64_t*) * tmp);
    if (out->EligibleEntities==0) {
        return -1;
    }
    out->EligibleEntities_ai.length = tmp;
    for (uint32_t index = 0; index < out->EligibleEntities_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->EligibleEntities[index]))
    }
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->RevisitRate)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Parameters = malloc(sizeof(KeyValuePair*) * tmp);
    if (out->Parameters==0) {
        return -1;
    }
    out->Parameters_ai.length = tmp;
    for (uint32_t index = 0; index < out->Parameters_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->Parameters[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_KeyValuePair(&(out->Parameters[index]));
            CHECK(lmcp_unpack_KeyValuePair(inb, size_remain, (out->Parameters[index])))
        }
    }
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->Priority)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->Required)))
    return 0;
}
size_t lmcp_pack_Task(uint8_t* buf, Task* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->TaskID);
    outb += lmcp_pack_uint16_t(outb, i->Label_ai.length);
    for (uint32_t index = 0; index < i->Label_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->Label[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->EligibleEntities_ai.length);
    for (uint32_t index = 0; index < i->EligibleEntities_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->EligibleEntities[index]);
    }
    outb += lmcp_pack_float(outb, i->RevisitRate);
    outb += lmcp_pack_uint16_t(outb, i->Parameters_ai.length);
    for (uint32_t index = 0; index < i->Parameters_ai.length; index++) {
        if (i->Parameters[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 2);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_KeyValuePair(outb, i->Parameters[index]);
        }
    }
    outb += lmcp_pack_uint8_t(outb, i->Priority);
    outb += lmcp_pack_uint8_t(outb, i->Required);
    return (outb - buf);
}

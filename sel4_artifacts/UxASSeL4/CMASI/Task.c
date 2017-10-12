
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Task.h"
#include "KeyValuePair.h"
void lmcp_pp_Task(Task* s) {
    printf("Task{");
    printf("taskid: ");
    printf("%lld",s->taskid);
    printf("\n");
    printf("label: ");
    printf("[");
    for (uint32_t index = 0; index < s->label_ai.length; index++) {
        printf("%c",s->label[index]);
        printf(",");
    }
    printf("\n");
    printf("eligibleentities: ");
    printf("[");
    for (uint32_t index = 0; index < s->eligibleentities_ai.length; index++) {
        printf("%lld",s->eligibleentities[index]);
        printf(",");
    }
    printf("\n");
    printf("revisitrate: ");
    printf("%u",s->revisitrate);
    printf("\n");
    printf("parameters: ");
    printf("[");
    for (uint32_t index = 0; index < s->parameters_ai.length; index++) {
        lmcp_pp_KeyValuePair((s->parameters[index]));
        printf(",");
    }
    printf("\n");
    printf("priority: ");
    printf("%u",s->priority);
    printf("\n");
    printf("required: ");
    printf("%u",s->required);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_Task (Task* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->label_ai.length; index++) {
        out += sizeof(char);
    }
    out += 2;
    for (uint32_t index = 0; index < i->eligibleentities_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += sizeof(uint32_t);
    out += 2;
    for (uint32_t index = 0; index < i->parameters_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->parameters[index]);
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
    if (out->label != NULL) {
        free(out->label);
    }
    if (out->eligibleentities != NULL) {
        free(out->eligibleentities);
    }
    if (out->parameters != NULL) {
        for (uint32_t index = 0; index < out->parameters_ai.length; index++) {
            if (out->parameters[index] != NULL) {
                lmcp_free_KeyValuePair(out->parameters[index], 1);
            }
        }
        free(out->parameters);
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
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->taskid)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->label = malloc(sizeof(char*) * tmp);
    if (out->label==0) {
        return -1;
    }
    out->label_ai.length = tmp;
    for (uint32_t index = 0; index < out->label_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->label[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->eligibleentities = malloc(sizeof(int64_t*) * tmp);
    if (out->eligibleentities==0) {
        return -1;
    }
    out->eligibleentities_ai.length = tmp;
    for (uint32_t index = 0; index < out->eligibleentities_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->eligibleentities[index]))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->revisitrate)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->parameters = malloc(sizeof(KeyValuePair*) * tmp);
    if (out->parameters==0) {
        return -1;
    }
    out->parameters_ai.length = tmp;
    for (uint32_t index = 0; index < out->parameters_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->parameters[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_KeyValuePair(&(out->parameters[index]));
            CHECK(lmcp_unpack_KeyValuePair(inb, size_remain, (out->parameters[index])))
        }
    }
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->priority)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->required)))
    return 0;
}
size_t lmcp_pack_Task(uint8_t* buf, Task* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->taskid);
    outb += lmcp_pack_uint16_t(outb, i->label_ai.length);
    for (uint32_t index = 0; index < i->label_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->label[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->eligibleentities_ai.length);
    for (uint32_t index = 0; index < i->eligibleentities_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->eligibleentities[index]);
    }
    outb += lmcp_pack_uint32_t(outb, i->revisitrate);
    outb += lmcp_pack_uint16_t(outb, i->parameters_ai.length);
    for (uint32_t index = 0; index < i->parameters_ai.length; index++) {
        if (i->parameters[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 2);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_KeyValuePair(outb, i->parameters[index]);
        }
    }
    outb += lmcp_pack_uint8_t(outb, i->priority);
    outb += lmcp_pack_uint8_t(outb, i->required);
    return (outb - buf);
}

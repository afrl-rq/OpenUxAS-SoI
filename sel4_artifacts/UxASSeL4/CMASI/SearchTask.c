
#include "common/struct_defines.h"
#include "common/conv.h"
#include "SearchTask.h"
#include "Task.h"
#include "enums.h"
void lmcp_pp_SearchTask(SearchTask* s) {
    printf("SearchTask{");
    printf("Inherited from Task:\n");
    lmcp_pp_Task(&(s->super));
    printf("desiredwavelengthbands: ");
    printf("[");
    for (uint32_t index = 0; index < s->desiredwavelengthbands_ai.length; index++) {
        printf("%i", s->desiredwavelengthbands[index]);
        printf(",");
    }
    printf("\n");
    printf("dwelltime: ");
    printf("%lld",s->dwelltime);
    printf("\n");
    printf("groundsampledistance: ");
    printf("%u",s->groundsampledistance);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_SearchTask (SearchTask* i) {
    size_t out = 0;
    out += lmcp_packsize_Task(&(i->super));
    out += 2;
    for (uint32_t index = 0; index < i->desiredwavelengthbands_ai.length; index++) {
        out += 4;
    }
    out += sizeof(int64_t);
    out += sizeof(uint32_t);
    return out;
}
size_t lmcp_pack_SearchTask_header(uint8_t* buf, SearchTask* i) {
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
    outb += lmcp_pack_uint32_t(outb, 9);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_SearchTask(SearchTask* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_Task(&(out->super), 0);
    if (out->desiredwavelengthbands != NULL) {
        free(out->desiredwavelengthbands);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_SearchTask (SearchTask** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(SearchTask));
    ((lmcp_object*)(*i)) -> type = 9;
}
int lmcp_unpack_SearchTask(uint8_t** inb, size_t *size_remain, SearchTask* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    SearchTask* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_Task(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->desiredwavelengthbands = malloc(sizeof(int32_t*) * tmp);
    if (out->desiredwavelengthbands==0) {
        return -1;
    }
    out->desiredwavelengthbands_ai.length = tmp;
    for (uint32_t index = 0; index < out->desiredwavelengthbands_ai.length; index++) {
        CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &out->desiredwavelengthbands[index]))
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->dwelltime)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->groundsampledistance)))
    return 0;
}
size_t lmcp_pack_SearchTask(uint8_t* buf, SearchTask* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_Task(outb, &(i->super));
    outb += lmcp_pack_uint16_t(outb, i->desiredwavelengthbands_ai.length);
    for (uint32_t index = 0; index < i->desiredwavelengthbands_ai.length; index++) {
        outb += lmcp_pack_int32_t(outb, (int) i->desiredwavelengthbands[index]);
    }
    outb += lmcp_pack_int64_t(outb, i->dwelltime);
    outb += lmcp_pack_uint32_t(outb, i->groundsampledistance);
    return (outb - buf);
}

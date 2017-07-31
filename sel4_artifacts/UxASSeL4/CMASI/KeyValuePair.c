
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "KeyValuePair.h"
void lmcp_pp_KeyValuePair(KeyValuePair* s) {
    printf("KeyValuePair{");
    printf("Key: ");
    printf("[");
    for (uint32_t index = 0; index < s->Key_ai.length; index++) {
        printf("%c",s->Key[index]);
        printf(",");
    }
    printf("\n");
    printf("Value: ");
    printf("[");
    for (uint32_t index = 0; index < s->Value_ai.length; index++) {
        printf("%c",s->Value[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_KeyValuePair (KeyValuePair* i) {
    size_t out = 0;
    out += 2;
    for (uint32_t index = 0; index < i->Key_ai.length; index++) {
        out += sizeof(char);
    }
    out += 2;
    for (uint32_t index = 0; index < i->Value_ai.length; index++) {
        out += sizeof(char);
    }
    return out;
}
size_t lmcp_pack_KeyValuePair_header(uint8_t* buf, KeyValuePair* i) {
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
    outb += lmcp_pack_uint32_t(outb, 2);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_KeyValuePair(KeyValuePair* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->Key != NULL) {
        free(out->Key);
    }
    if (out->Value != NULL) {
        free(out->Value);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_KeyValuePair (KeyValuePair** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(KeyValuePair));
    ((lmcp_object*)(*i)) -> type = 2;
}
int lmcp_unpack_KeyValuePair(uint8_t** inb, size_t *size_remain, KeyValuePair* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    KeyValuePair* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Key = malloc(sizeof(char*) * tmp);
    if (out->Key==0) {
        return -1;
    }
    out->Key_ai.length = tmp;
    for (uint32_t index = 0; index < out->Key_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->Key[index]))
    }
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Value = malloc(sizeof(char*) * tmp);
    if (out->Value==0) {
        return -1;
    }
    out->Value_ai.length = tmp;
    for (uint32_t index = 0; index < out->Value_ai.length; index++) {
        CHECK(lmcp_unpack_char(inb, size_remain, &out->Value[index]))
    }
    return 0;
}
size_t lmcp_pack_KeyValuePair(uint8_t* buf, KeyValuePair* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint16_t(outb, i->Key_ai.length);
    for (uint32_t index = 0; index < i->Key_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->Key[index]);
    }
    outb += lmcp_pack_uint16_t(outb, i->Value_ai.length);
    for (uint32_t index = 0; index < i->Value_ai.length; index++) {
        outb += lmcp_pack_char(outb, i->Value[index]);
    }
    return (outb - buf);
}


#include "common/struct_defines.h"
#include "common/conv.h"
#include "GimbalConfiguration.h"
#include "PayloadConfiguration.h"
#include "enums.h"
void lmcp_pp_GimbalConfiguration(GimbalConfiguration* s) {
    printf("GimbalConfiguration{");
    printf("Inherited from PayloadConfiguration:\n");
    lmcp_pp_PayloadConfiguration(&(s->super));
    printf("supportedpointingmodes: ");
    printf("[");
    for (uint32_t index = 0; index < s->supportedpointingmodes_ai.length; index++) {
        printf("%i", s->supportedpointingmodes[index]);
        printf(",");
    }
    printf("\n");
    printf("minazimuth: ");
    printf("%u",s->minazimuth);
    printf("\n");
    printf("maxazimuth: ");
    printf("%u",s->maxazimuth);
    printf("\n");
    printf("isazimuthclamped: ");
    printf("%u",s->isazimuthclamped);
    printf("\n");
    printf("minelevation: ");
    printf("%u",s->minelevation);
    printf("\n");
    printf("maxelevation: ");
    printf("%u",s->maxelevation);
    printf("\n");
    printf("iselevationclamped: ");
    printf("%u",s->iselevationclamped);
    printf("\n");
    printf("minrotation: ");
    printf("%u",s->minrotation);
    printf("\n");
    printf("maxrotation: ");
    printf("%u",s->maxrotation);
    printf("\n");
    printf("isrotationclamped: ");
    printf("%u",s->isrotationclamped);
    printf("\n");
    printf("maxazimuthslewrate: ");
    printf("%u",s->maxazimuthslewrate);
    printf("\n");
    printf("maxelevationslewrate: ");
    printf("%u",s->maxelevationslewrate);
    printf("\n");
    printf("maxrotationrate: ");
    printf("%u",s->maxrotationrate);
    printf("\n");
    printf("containedpayloadlist: ");
    printf("[");
    for (uint32_t index = 0; index < s->containedpayloadlist_ai.length; index++) {
        printf("%lld",s->containedpayloadlist[index]);
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_GimbalConfiguration (GimbalConfiguration* i) {
    size_t out = 0;
    out += lmcp_packsize_PayloadConfiguration(&(i->super));
    out += 2;
    for (uint32_t index = 0; index < i->supportedpointingmodes_ai.length; index++) {
        out += 4;
    }
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint8_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint8_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint8_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += 2;
    for (uint32_t index = 0; index < i->containedpayloadlist_ai.length; index++) {
        out += sizeof(int64_t);
    }
    return out;
}
size_t lmcp_pack_GimbalConfiguration_header(uint8_t* buf, GimbalConfiguration* i) {
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
    outb += lmcp_pack_uint32_t(outb, 24);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_GimbalConfiguration(GimbalConfiguration* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_PayloadConfiguration(&(out->super), 0);
    if (out->supportedpointingmodes != NULL) {
        free(out->supportedpointingmodes);
    }
    if (out->containedpayloadlist != NULL) {
        free(out->containedpayloadlist);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_GimbalConfiguration (GimbalConfiguration** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(GimbalConfiguration));
    ((lmcp_object*)(*i)) -> type = 24;
}
int lmcp_unpack_GimbalConfiguration(uint8_t** inb, size_t *size_remain, GimbalConfiguration* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    GimbalConfiguration* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_PayloadConfiguration(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->supportedpointingmodes = malloc(sizeof(int32_t*) * tmp);
    if (out->supportedpointingmodes==0) {
        return -1;
    }
    out->supportedpointingmodes_ai.length = tmp;
    for (uint32_t index = 0; index < out->supportedpointingmodes_ai.length; index++) {
        CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &out->supportedpointingmodes[index]))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->minazimuth)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maxazimuth)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->isazimuthclamped)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->minelevation)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maxelevation)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->iselevationclamped)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->minrotation)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maxrotation)))
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &(out->isrotationclamped)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maxazimuthslewrate)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maxelevationslewrate)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->maxrotationrate)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->containedpayloadlist = malloc(sizeof(int64_t*) * tmp);
    if (out->containedpayloadlist==0) {
        return -1;
    }
    out->containedpayloadlist_ai.length = tmp;
    for (uint32_t index = 0; index < out->containedpayloadlist_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->containedpayloadlist[index]))
    }
    return 0;
}
size_t lmcp_pack_GimbalConfiguration(uint8_t* buf, GimbalConfiguration* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_PayloadConfiguration(outb, &(i->super));
    outb += lmcp_pack_uint16_t(outb, i->supportedpointingmodes_ai.length);
    for (uint32_t index = 0; index < i->supportedpointingmodes_ai.length; index++) {
        outb += lmcp_pack_int32_t(outb, (int) i->supportedpointingmodes[index]);
    }
    outb += lmcp_pack_uint32_t(outb, i->minazimuth);
    outb += lmcp_pack_uint32_t(outb, i->maxazimuth);
    outb += lmcp_pack_uint8_t(outb, i->isazimuthclamped);
    outb += lmcp_pack_uint32_t(outb, i->minelevation);
    outb += lmcp_pack_uint32_t(outb, i->maxelevation);
    outb += lmcp_pack_uint8_t(outb, i->iselevationclamped);
    outb += lmcp_pack_uint32_t(outb, i->minrotation);
    outb += lmcp_pack_uint32_t(outb, i->maxrotation);
    outb += lmcp_pack_uint8_t(outb, i->isrotationclamped);
    outb += lmcp_pack_uint32_t(outb, i->maxazimuthslewrate);
    outb += lmcp_pack_uint32_t(outb, i->maxelevationslewrate);
    outb += lmcp_pack_uint32_t(outb, i->maxrotationrate);
    outb += lmcp_pack_uint16_t(outb, i->containedpayloadlist_ai.length);
    for (uint32_t index = 0; index < i->containedpayloadlist_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->containedpayloadlist[index]);
    }
    return (outb - buf);
}

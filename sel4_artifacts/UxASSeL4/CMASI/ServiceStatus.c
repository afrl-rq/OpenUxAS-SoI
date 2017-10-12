
#include "common/struct_defines.h"
#include "common/conv.h"
#include "ServiceStatus.h"
#include "KeyValuePair.h"
#include "enums.h"
void lmcp_pp_ServiceStatus(ServiceStatus* s) {
    printf("ServiceStatus{");
    printf("percentcomplete: ");
    printf("%u",s->percentcomplete);
    printf("\n");
    printf("info: ");
    printf("[");
    for (uint32_t index = 0; index < s->info_ai.length; index++) {
        lmcp_pp_KeyValuePair((s->info[index]));
        printf(",");
    }
    printf("\n");
    printf("statustype: ");
    printf("%i", s->statustype);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_ServiceStatus (ServiceStatus* i) {
    size_t out = 0;
    out += sizeof(uint32_t);
    out += 2;
    for (uint32_t index = 0; index < i->info_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->info[index]);
    }
    out += 4;
    return out;
}
size_t lmcp_pack_ServiceStatus_header(uint8_t* buf, ServiceStatus* i) {
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
    outb += lmcp_pack_uint32_t(outb, 45);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_ServiceStatus(ServiceStatus* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->info != NULL) {
        for (uint32_t index = 0; index < out->info_ai.length; index++) {
            if (out->info[index] != NULL) {
                lmcp_free_KeyValuePair(out->info[index], 1);
            }
        }
        free(out->info);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_ServiceStatus (ServiceStatus** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(ServiceStatus));
    ((lmcp_object*)(*i)) -> type = 45;
}
int lmcp_unpack_ServiceStatus(uint8_t** inb, size_t *size_remain, ServiceStatus* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    ServiceStatus* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->percentcomplete)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->info = malloc(sizeof(KeyValuePair*) * tmp);
    if (out->info==0) {
        return -1;
    }
    out->info_ai.length = tmp;
    for (uint32_t index = 0; index < out->info_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->info[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_KeyValuePair(&(out->info[index]));
            CHECK(lmcp_unpack_KeyValuePair(inb, size_remain, (out->info[index])))
        }
    }
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->statustype)))
    return 0;
}
size_t lmcp_pack_ServiceStatus(uint8_t* buf, ServiceStatus* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_uint32_t(outb, i->percentcomplete);
    outb += lmcp_pack_uint16_t(outb, i->info_ai.length);
    for (uint32_t index = 0; index < i->info_ai.length; index++) {
        if (i->info[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 2);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_KeyValuePair(outb, i->info[index]);
        }
    }
    outb += lmcp_pack_int32_t(outb, (int) i->statustype);
    return (outb - buf);
}

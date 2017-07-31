
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "ServiceStatus.h"
#include "KeyValuePair.h"
#include "enums.h"
void lmcp_pp_ServiceStatus(ServiceStatus* s) {
    printf("ServiceStatus{");
    printf("PercentComplete: ");
    printf("%f",s->PercentComplete);
    printf("\n");
    printf("Info: ");
    printf("[");
    for (uint32_t index = 0; index < s->Info_ai.length; index++) {
        lmcp_pp_KeyValuePair((s->Info[index]));
        printf(",");
    }
    printf("\n");
    printf("StatusType: ");
    printf("%i", s->StatusType);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_ServiceStatus (ServiceStatus* i) {
    size_t out = 0;
    out += sizeof(float);
    out += 2;
    for (uint32_t index = 0; index < i->Info_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->Info[index]);
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
    if (out->Info != NULL) {
        for (uint32_t index = 0; index < out->Info_ai.length; index++) {
            if (out->Info[index] != NULL) {
                lmcp_free_KeyValuePair(out->Info[index], 1);
            }
        }
        free(out->Info);
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
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->PercentComplete)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Info = malloc(sizeof(KeyValuePair*) * tmp);
    if (out->Info==0) {
        return -1;
    }
    out->Info_ai.length = tmp;
    for (uint32_t index = 0; index < out->Info_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->Info[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_KeyValuePair(&(out->Info[index]));
            CHECK(lmcp_unpack_KeyValuePair(inb, size_remain, (out->Info[index])))
        }
    }
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->StatusType)))
    return 0;
}
size_t lmcp_pack_ServiceStatus(uint8_t* buf, ServiceStatus* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_float(outb, i->PercentComplete);
    outb += lmcp_pack_uint16_t(outb, i->Info_ai.length);
    for (uint32_t index = 0; index < i->Info_ai.length; index++) {
        if (i->Info[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 2);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_KeyValuePair(outb, i->Info[index]);
        }
    }
    outb += lmcp_pack_int32_t(outb, (int) i->StatusType);
    return (outb - buf);
}

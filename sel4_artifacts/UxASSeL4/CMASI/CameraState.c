
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "CameraState.h"
#include "GimballedPayloadState.h"
#include "Location3D.h"
#include "Location3D.h"
void lmcp_pp_CameraState(CameraState* s) {
    printf("CameraState{");
    printf("Inherited from GimballedPayloadState:\n");
    lmcp_pp_GimballedPayloadState(&(s->super));
    printf("HorizontalFieldOfView: ");
    printf("%f",s->HorizontalFieldOfView);
    printf("\n");
    printf("VerticalFieldOfView: ");
    printf("%f",s->VerticalFieldOfView);
    printf("\n");
    printf("Footprint: ");
    printf("[");
    for (uint32_t index = 0; index < s->Footprint_ai.length; index++) {
        lmcp_pp_Location3D((s->Footprint[index]));
        printf(",");
    }
    printf("\n");
    printf("Centerpoint: ");
    lmcp_pp_Location3D((s->Centerpoint));
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_CameraState (CameraState* i) {
    size_t out = 0;
    out += lmcp_packsize_GimballedPayloadState(&(i->super));
    out += sizeof(float);
    out += sizeof(float);
    out += 2;
    for (uint32_t index = 0; index < i->Footprint_ai.length; index++) {
        out += 15 + lmcp_packsize_Location3D(i->Footprint[index]);
    }
    if (i->Centerpoint==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_Location3D(i->Centerpoint);
    }
    return out;
}
size_t lmcp_pack_CameraState_header(uint8_t* buf, CameraState* i) {
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
    outb += lmcp_pack_uint32_t(outb, 21);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_CameraState(CameraState* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_GimballedPayloadState(&(out->super), 0);
    if (out->Footprint != NULL) {
        for (uint32_t index = 0; index < out->Footprint_ai.length; index++) {
            if (out->Footprint[index] != NULL) {
                lmcp_free_Location3D(out->Footprint[index], 1);
            }
        }
        free(out->Footprint);
    }
    if (out->Centerpoint != NULL) {
        lmcp_free_Location3D(out->Centerpoint, 1);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_CameraState (CameraState** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(CameraState));
    ((lmcp_object*)(*i)) -> type = 21;
}
int lmcp_unpack_CameraState(uint8_t** inb, size_t *size_remain, CameraState* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    CameraState* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_GimballedPayloadState(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->HorizontalFieldOfView)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->VerticalFieldOfView)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->Footprint = malloc(sizeof(Location3D*) * tmp);
    if (out->Footprint==0) {
        return -1;
    }
    out->Footprint_ai.length = tmp;
    for (uint32_t index = 0; index < out->Footprint_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->Footprint[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_Location3D(&(out->Footprint[index]));
            CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->Footprint[index])))
        }
    }
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->Centerpoint = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_Location3D(&(out->Centerpoint));
        CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->Centerpoint)))
    }
    return 0;
}
size_t lmcp_pack_CameraState(uint8_t* buf, CameraState* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_GimballedPayloadState(outb, &(i->super));
    outb += lmcp_pack_float(outb, i->HorizontalFieldOfView);
    outb += lmcp_pack_float(outb, i->VerticalFieldOfView);
    outb += lmcp_pack_uint16_t(outb, i->Footprint_ai.length);
    for (uint32_t index = 0; index < i->Footprint_ai.length; index++) {
        if (i->Footprint[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 3);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_Location3D(outb, i->Footprint[index]);
        }
    }
    if (i->Centerpoint==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 3);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_Location3D(outb, i->Centerpoint);
    }
    return (outb - buf);
}

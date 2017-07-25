
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "CameraAction.h"
#include "PayloadAction.h"
#include "PayloadAction.h"
void lmcp_pp_CameraAction(CameraAction* s) {
    printf("CameraAction{");
    printf("Inherited from PayloadAction:\n");
    lmcp_pp_PayloadAction(&(s->super));
    printf("HorizontalFieldOfView: ");
    printf("%f",s->HorizontalFieldOfView);
    printf("\n");
    printf("AssociatedActions: ");
    printf("[");
    for (uint32_t index = 0; index < s->AssociatedActions_ai.length; index++) {
        lmcp_pp_PayloadAction((s->AssociatedActions[index]));
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_CameraAction (CameraAction* i) {
    size_t out = 0;
    out += lmcp_packsize_PayloadAction(&(i->super));
    out += sizeof(float);
    out += 2;
    for (uint32_t index = 0; index < i->AssociatedActions_ai.length; index++) {
        out += 15 + lmcp_packsize_PayloadAction(i->AssociatedActions[index]);
    }
    return out;
}
size_t lmcp_pack_CameraAction_header(uint8_t* buf, CameraAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 18);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_CameraAction(CameraAction* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_PayloadAction(&(out->super), 0);
    if (out->AssociatedActions != NULL) {
        for (uint32_t index = 0; index < out->AssociatedActions_ai.length; index++) {
            if (out->AssociatedActions[index] != NULL) {
                lmcp_free_PayloadAction(out->AssociatedActions[index], 1);
            }
        }
        free(out->AssociatedActions);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_CameraAction (CameraAction** i) {
    if (i == NULL) return;
    (*i) = malloc(sizeof(CameraAction));
    *(*i) = (const CameraAction) {
        0
    };
    ((lmcp_object*)(*i)) -> type = 18;
}
int lmcp_unpack_CameraAction(uint8_t** inb, size_t *size_remain, CameraAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    CameraAction* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_PayloadAction(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->HorizontalFieldOfView)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->AssociatedActions = malloc(sizeof(PayloadAction*) * tmp);
    if (out->AssociatedActions==0) {
        return -1;
    }
    out->AssociatedActions_ai.length = tmp;
    for (uint32_t index = 0; index < out->AssociatedActions_ai.length; index++) {
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->AssociatedActions[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_PayloadAction(&(out->AssociatedActions[index]));
            CHECK(lmcp_unpack_PayloadAction(inb, size_remain, (out->AssociatedActions[index])))
        }
    }
    return 0;
}
size_t lmcp_pack_CameraAction(uint8_t* buf, CameraAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_PayloadAction(outb, &(i->super));
    outb += lmcp_pack_float(outb, i->HorizontalFieldOfView);
    outb += lmcp_pack_uint16_t(outb, i->AssociatedActions_ai.length);
    for (uint32_t index = 0; index < i->AssociatedActions_ai.length; index++) {
        if (i->AssociatedActions[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 4);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_PayloadAction(outb, i->AssociatedActions[index]);
        }
    }
    return (outb - buf);
}

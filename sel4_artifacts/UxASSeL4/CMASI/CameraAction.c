
#include "common/struct_defines.h"
#include "common/conv.h"
#include "CameraAction.h"
#include "PayloadAction.h"
#include "PayloadAction.h"
void lmcp_pp_CameraAction(CameraAction* s) {
    printf("CameraAction{");
    printf("Inherited from PayloadAction:\n");
    lmcp_pp_PayloadAction(&(s->super));
    printf("horizontalfieldofview: ");
    printf("%u",s->horizontalfieldofview);
    printf("\n");
    printf("associatedactions: ");
    printf("[");
    for (uint32_t index = 0; index < s->associatedactions_ai.length; index++) {
        lmcp_pp_PayloadAction((s->associatedactions[index]));
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_CameraAction (CameraAction* i) {
    size_t out = 0;
    out += lmcp_packsize_PayloadAction(&(i->super));
    out += sizeof(uint32_t);
    out += 2;
    for (uint32_t index = 0; index < i->associatedactions_ai.length; index++) {
        out += 15 + lmcp_packsize_PayloadAction(i->associatedactions[index]);
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
    if (out->associatedactions != NULL) {
        for (uint32_t index = 0; index < out->associatedactions_ai.length; index++) {
            if (out->associatedactions[index] != NULL) {
                lmcp_free_PayloadAction(out->associatedactions[index], 1);
            }
        }
        free(out->associatedactions);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_CameraAction (CameraAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(CameraAction));
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
    CHECK(lmcp_unpack_PayloadAction(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->horizontalfieldofview)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->associatedactions = malloc(sizeof(PayloadAction*) * tmp);
    if (out->associatedactions==0) {
        return -1;
    }
    out->associatedactions_ai.length = tmp;
    for (uint32_t index = 0; index < out->associatedactions_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->associatedactions[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_PayloadAction(&(out->associatedactions[index]));
            CHECK(lmcp_unpack_PayloadAction(inb, size_remain, (out->associatedactions[index])))
        }
    }
    return 0;
}
size_t lmcp_pack_CameraAction(uint8_t* buf, CameraAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_PayloadAction(outb, &(i->super));
    outb += lmcp_pack_uint32_t(outb, i->horizontalfieldofview);
    outb += lmcp_pack_uint16_t(outb, i->associatedactions_ai.length);
    for (uint32_t index = 0; index < i->associatedactions_ai.length; index++) {
        if (i->associatedactions[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 4);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_PayloadAction(outb, i->associatedactions[index]);
        }
    }
    return (outb - buf);
}

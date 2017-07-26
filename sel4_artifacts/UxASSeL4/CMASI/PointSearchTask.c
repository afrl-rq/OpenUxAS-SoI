
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PointSearchTask.h"
#include "SearchTask.h"
#include "Location3D.h"
#include "Wedge.h"
void lmcp_pp_PointSearchTask(PointSearchTask* s) {
    printf("PointSearchTask{");
    printf("Inherited from SearchTask:\n");
    lmcp_pp_SearchTask(&(s->super));
    printf("SearchLocation: ");
    lmcp_pp_Location3D((s->SearchLocation));
    printf("\n");
    printf("StandoffDistance: ");
    printf("%f",s->StandoffDistance);
    printf("\n");
    printf("ViewAngleList: ");
    printf("[");
    for (uint32_t index = 0; index < s->ViewAngleList_ai.length; index++) {
        lmcp_pp_Wedge((s->ViewAngleList[index]));
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_PointSearchTask (PointSearchTask* i) {
    size_t out = 0;
    out += lmcp_packsize_SearchTask(&(i->super));
    if (i->SearchLocation==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_Location3D(i->SearchLocation);
    }
    out += sizeof(float);
    out += 2;
    for (uint32_t index = 0; index < i->ViewAngleList_ai.length; index++) {
        out += 15 + lmcp_packsize_Wedge(i->ViewAngleList[index]);
    }
    return out;
}
size_t lmcp_pack_PointSearchTask_header(uint8_t* buf, PointSearchTask* i) {
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
    outb += lmcp_pack_uint32_t(outb, 41);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_PointSearchTask(PointSearchTask* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_SearchTask(&(out->super), 0);
    if (out->SearchLocation != NULL) {
        lmcp_free_Location3D(out->SearchLocation, 1);
    }
    if (out->ViewAngleList != NULL) {
        for (uint32_t index = 0; index < out->ViewAngleList_ai.length; index++) {
            if (out->ViewAngleList[index] != NULL) {
                lmcp_free_Wedge(out->ViewAngleList[index], 1);
            }
        }
        free(out->ViewAngleList);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_PointSearchTask (PointSearchTask** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(PointSearchTask));
    ((lmcp_object*)(*i)) -> type = 41;
}
int lmcp_unpack_PointSearchTask(uint8_t** inb, size_t *size_remain, PointSearchTask* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    PointSearchTask* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_SearchTask(inb, size_remain, &(out->super)))
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->SearchLocation = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_Location3D(&(out->SearchLocation));
        CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->SearchLocation)))
    }
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->StandoffDistance)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->ViewAngleList = malloc(sizeof(Wedge*) * tmp);
    if (out->ViewAngleList==0) {
        return -1;
    }
    out->ViewAngleList_ai.length = tmp;
    for (uint32_t index = 0; index < out->ViewAngleList_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->ViewAngleList[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_Wedge(&(out->ViewAngleList[index]));
            CHECK(lmcp_unpack_Wedge(inb, size_remain, (out->ViewAngleList[index])))
        }
    }
    return 0;
}
size_t lmcp_pack_PointSearchTask(uint8_t* buf, PointSearchTask* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_SearchTask(outb, &(i->super));
    if (i->SearchLocation==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 3);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_Location3D(outb, i->SearchLocation);
    }
    outb += lmcp_pack_float(outb, i->StandoffDistance);
    outb += lmcp_pack_uint16_t(outb, i->ViewAngleList_ai.length);
    for (uint32_t index = 0; index < i->ViewAngleList_ai.length; index++) {
        if (i->ViewAngleList[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 16);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_Wedge(outb, i->ViewAngleList[index]);
        }
    }
    return (outb - buf);
}

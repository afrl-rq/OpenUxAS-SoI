
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
    printf("searchlocation: ");
    lmcp_pp_Location3D((s->searchlocation));
    printf("\n");
    printf("standoffdistance: ");
    printf("%u",s->standoffdistance);
    printf("\n");
    printf("viewanglelist: ");
    printf("[");
    for (uint32_t index = 0; index < s->viewanglelist_ai.length; index++) {
        lmcp_pp_Wedge((s->viewanglelist[index]));
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_PointSearchTask (PointSearchTask* i) {
    size_t out = 0;
    out += lmcp_packsize_SearchTask(&(i->super));
    if (i->searchlocation==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_Location3D(i->searchlocation);
    }
    out += sizeof(uint32_t);
    out += 2;
    for (uint32_t index = 0; index < i->viewanglelist_ai.length; index++) {
        out += 15 + lmcp_packsize_Wedge(i->viewanglelist[index]);
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
    if (out->searchlocation != NULL) {
        lmcp_free_Location3D(out->searchlocation, 1);
    }
    if (out->viewanglelist != NULL) {
        for (uint32_t index = 0; index < out->viewanglelist_ai.length; index++) {
            if (out->viewanglelist[index] != NULL) {
                lmcp_free_Wedge(out->viewanglelist[index], 1);
            }
        }
        free(out->viewanglelist);
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
        out->searchlocation = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_Location3D(&(out->searchlocation));
        CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->searchlocation)))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->standoffdistance)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->viewanglelist = malloc(sizeof(Wedge*) * tmp);
    if (out->viewanglelist==0) {
        return -1;
    }
    out->viewanglelist_ai.length = tmp;
    for (uint32_t index = 0; index < out->viewanglelist_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->viewanglelist[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_Wedge(&(out->viewanglelist[index]));
            CHECK(lmcp_unpack_Wedge(inb, size_remain, (out->viewanglelist[index])))
        }
    }
    return 0;
}
size_t lmcp_pack_PointSearchTask(uint8_t* buf, PointSearchTask* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_SearchTask(outb, &(i->super));
    if (i->searchlocation==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 3);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_Location3D(outb, i->searchlocation);
    }
    outb += lmcp_pack_uint32_t(outb, i->standoffdistance);
    outb += lmcp_pack_uint16_t(outb, i->viewanglelist_ai.length);
    for (uint32_t index = 0; index < i->viewanglelist_ai.length; index++) {
        if (i->viewanglelist[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 16);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_Wedge(outb, i->viewanglelist[index]);
        }
    }
    return (outb - buf);
}

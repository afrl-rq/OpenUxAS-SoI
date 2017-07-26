
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Polygon.h"
#include "AbstractGeometry.h"
#include "Location3D.h"
void lmcp_pp_Polygon(Polygon* s) {
    printf("Polygon{");
    printf("Inherited from AbstractGeometry:\n");
    lmcp_pp_AbstractGeometry(&(s->super));
    printf("BoundaryPoints: ");
    printf("[");
    for (uint32_t index = 0; index < s->BoundaryPoints_ai.length; index++) {
        lmcp_pp_Location3D((s->BoundaryPoints[index]));
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_Polygon (Polygon* i) {
    size_t out = 0;
    out += lmcp_packsize_AbstractGeometry(&(i->super));
    out += 2;
    for (uint32_t index = 0; index < i->BoundaryPoints_ai.length; index++) {
        out += 15 + lmcp_packsize_Location3D(i->BoundaryPoints[index]);
    }
    return out;
}
size_t lmcp_pack_Polygon_header(uint8_t* buf, Polygon* i) {
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
    outb += lmcp_pack_uint32_t(outb, 42);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_Polygon(Polygon* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_AbstractGeometry(&(out->super), 0);
    if (out->BoundaryPoints != NULL) {
        for (uint32_t index = 0; index < out->BoundaryPoints_ai.length; index++) {
            if (out->BoundaryPoints[index] != NULL) {
                lmcp_free_Location3D(out->BoundaryPoints[index], 1);
            }
        }
        free(out->BoundaryPoints);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_Polygon (Polygon** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(Polygon));
    ((lmcp_object*)(*i)) -> type = 42;
}
int lmcp_unpack_Polygon(uint8_t** inb, size_t *size_remain, Polygon* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    Polygon* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_AbstractGeometry(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->BoundaryPoints = malloc(sizeof(Location3D*) * tmp);
    if (out->BoundaryPoints==0) {
        return -1;
    }
    out->BoundaryPoints_ai.length = tmp;
    for (uint32_t index = 0; index < out->BoundaryPoints_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->BoundaryPoints[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_Location3D(&(out->BoundaryPoints[index]));
            CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->BoundaryPoints[index])))
        }
    }
    return 0;
}
size_t lmcp_pack_Polygon(uint8_t* buf, Polygon* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_AbstractGeometry(outb, &(i->super));
    outb += lmcp_pack_uint16_t(outb, i->BoundaryPoints_ai.length);
    for (uint32_t index = 0; index < i->BoundaryPoints_ai.length; index++) {
        if (i->BoundaryPoints[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 3);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_Location3D(outb, i->BoundaryPoints[index]);
        }
    }
    return (outb - buf);
}

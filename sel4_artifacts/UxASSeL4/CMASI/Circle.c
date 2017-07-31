
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Circle.h"
#include "AbstractGeometry.h"
#include "Location3D.h"
void lmcp_pp_Circle(Circle* s) {
    printf("Circle{");
    printf("Inherited from AbstractGeometry:\n");
    lmcp_pp_AbstractGeometry(&(s->super));
    printf("CenterPoint: ");
    lmcp_pp_Location3D((s->CenterPoint));
    printf("\n");
    printf("Radius: ");
    printf("%f",s->Radius);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_Circle (Circle* i) {
    size_t out = 0;
    out += lmcp_packsize_AbstractGeometry(&(i->super));
    if (i->CenterPoint==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_Location3D(i->CenterPoint);
    }
    out += sizeof(float);
    return out;
}
size_t lmcp_pack_Circle_header(uint8_t* buf, Circle* i) {
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
    outb += lmcp_pack_uint32_t(outb, 22);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_Circle(Circle* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_AbstractGeometry(&(out->super), 0);
    if (out->CenterPoint != NULL) {
        lmcp_free_Location3D(out->CenterPoint, 1);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_Circle (Circle** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(Circle));
    ((lmcp_object*)(*i)) -> type = 22;
}
int lmcp_unpack_Circle(uint8_t** inb, size_t *size_remain, Circle* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    Circle* out = outp;
    CHECK(lmcp_unpack_AbstractGeometry(inb, size_remain, &(out->super)))
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->CenterPoint = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_Location3D(&(out->CenterPoint));
        CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->CenterPoint)))
    }
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Radius)))
    return 0;
}
size_t lmcp_pack_Circle(uint8_t* buf, Circle* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_AbstractGeometry(outb, &(i->super));
    if (i->CenterPoint==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 3);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_Location3D(outb, i->CenterPoint);
    }
    outb += lmcp_pack_float(outb, i->Radius);
    return (outb - buf);
}

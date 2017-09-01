
#include "common/struct_defines.h"
#include "common/conv.h"
#include "Rectangle.h"
#include "AbstractGeometry.h"
#include "Location3D.h"
void lmcp_pp_Rectangle(Rectangle* s) {
    printf("Rectangle{");
    printf("Inherited from AbstractGeometry:\n");
    lmcp_pp_AbstractGeometry(&(s->super));
    printf("centerpoint: ");
    lmcp_pp_Location3D((s->centerpoint));
    printf("\n");
    printf("width: ");
    printf("%u",s->width);
    printf("\n");
    printf("height: ");
    printf("%u",s->height);
    printf("\n");
    printf("rotation: ");
    printf("%u",s->rotation);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_Rectangle (Rectangle* i) {
    size_t out = 0;
    out += lmcp_packsize_AbstractGeometry(&(i->super));
    if (i->centerpoint==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_Location3D(i->centerpoint);
    }
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    return out;
}
size_t lmcp_pack_Rectangle_header(uint8_t* buf, Rectangle* i) {
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
    outb += lmcp_pack_uint32_t(outb, 43);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_Rectangle(Rectangle* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_AbstractGeometry(&(out->super), 0);
    if (out->centerpoint != NULL) {
        lmcp_free_Location3D(out->centerpoint, 1);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_Rectangle (Rectangle** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(Rectangle));
    ((lmcp_object*)(*i)) -> type = 43;
}
int lmcp_unpack_Rectangle(uint8_t** inb, size_t *size_remain, Rectangle* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    Rectangle* out = outp;
    CHECK(lmcp_unpack_AbstractGeometry(inb, size_remain, &(out->super)))
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->centerpoint = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_Location3D(&(out->centerpoint));
        CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->centerpoint)))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->width)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->height)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->rotation)))
    return 0;
}
size_t lmcp_pack_Rectangle(uint8_t* buf, Rectangle* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_AbstractGeometry(outb, &(i->super));
    if (i->centerpoint==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 3);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_Location3D(outb, i->centerpoint);
    }
    outb += lmcp_pack_uint32_t(outb, i->width);
    outb += lmcp_pack_uint32_t(outb, i->height);
    outb += lmcp_pack_uint32_t(outb, i->rotation);
    return (outb - buf);
}

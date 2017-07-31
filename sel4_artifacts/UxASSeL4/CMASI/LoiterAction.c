
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "LoiterAction.h"
#include "NavigationAction.h"
#include "enums.h"
#include "Location3D.h"
void lmcp_pp_LoiterAction(LoiterAction* s) {
    printf("LoiterAction{");
    printf("Inherited from NavigationAction:\n");
    lmcp_pp_NavigationAction(&(s->super));
    printf("LoiterType: ");
    printf("%i", s->LoiterType);
    printf("\n");
    printf("Radius: ");
    printf("%f",s->Radius);
    printf("\n");
    printf("Axis: ");
    printf("%f",s->Axis);
    printf("\n");
    printf("Length: ");
    printf("%f",s->Length);
    printf("\n");
    printf("Direction: ");
    printf("%i", s->Direction);
    printf("\n");
    printf("Duration: ");
    printf("%lld",s->Duration);
    printf("\n");
    printf("Airspeed: ");
    printf("%f",s->Airspeed);
    printf("\n");
    printf("Location: ");
    lmcp_pp_Location3D((s->Location));
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_LoiterAction (LoiterAction* i) {
    size_t out = 0;
    out += lmcp_packsize_NavigationAction(&(i->super));
    out += 4;
    out += sizeof(float);
    out += sizeof(float);
    out += sizeof(float);
    out += 4;
    out += sizeof(int64_t);
    out += sizeof(float);
    if (i->Location==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_Location3D(i->Location);
    }
    return out;
}
size_t lmcp_pack_LoiterAction_header(uint8_t* buf, LoiterAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 33);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_LoiterAction(LoiterAction* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_NavigationAction(&(out->super), 0);
    if (out->Location != NULL) {
        lmcp_free_Location3D(out->Location, 1);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_LoiterAction (LoiterAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(LoiterAction));
    ((lmcp_object*)(*i)) -> type = 33;
}
int lmcp_unpack_LoiterAction(uint8_t** inb, size_t *size_remain, LoiterAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    LoiterAction* out = outp;
    CHECK(lmcp_unpack_NavigationAction(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->LoiterType)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Radius)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Axis)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Length)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->Direction)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->Duration)))
    CHECK(lmcp_unpack_float(inb, size_remain, &(out->Airspeed)))
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->Location = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_Location3D(&(out->Location));
        CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->Location)))
    }
    return 0;
}
size_t lmcp_pack_LoiterAction(uint8_t* buf, LoiterAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_NavigationAction(outb, &(i->super));
    outb += lmcp_pack_int32_t(outb, (int) i->LoiterType);
    outb += lmcp_pack_float(outb, i->Radius);
    outb += lmcp_pack_float(outb, i->Axis);
    outb += lmcp_pack_float(outb, i->Length);
    outb += lmcp_pack_int32_t(outb, (int) i->Direction);
    outb += lmcp_pack_int64_t(outb, i->Duration);
    outb += lmcp_pack_float(outb, i->Airspeed);
    if (i->Location==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 3);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_Location3D(outb, i->Location);
    }
    return (outb - buf);
}

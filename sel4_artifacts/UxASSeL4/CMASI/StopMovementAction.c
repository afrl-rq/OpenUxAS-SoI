
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "StopMovementAction.h"
#include "VehicleAction.h"
#include "Location3D.h"
void lmcp_pp_StopMovementAction(StopMovementAction* s) {
    printf("StopMovementAction{");
    printf("Inherited from VehicleAction:\n");
    lmcp_pp_VehicleAction(&(s->super));
    printf("Location: ");
    lmcp_pp_Location3D((s->Location));
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_StopMovementAction (StopMovementAction* i) {
    size_t out = 0;
    out += lmcp_packsize_VehicleAction(&(i->super));
    if (i->Location==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_Location3D(i->Location);
    }
    return out;
}
size_t lmcp_pack_StopMovementAction_header(uint8_t* buf, StopMovementAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 58);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_StopMovementAction(StopMovementAction* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_VehicleAction(&(out->super), 0);
    if (out->Location != NULL) {
        lmcp_free_Location3D(out->Location, 1);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_StopMovementAction (StopMovementAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(StopMovementAction));
    ((lmcp_object*)(*i)) -> type = 58;
}
int lmcp_unpack_StopMovementAction(uint8_t** inb, size_t *size_remain, StopMovementAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    StopMovementAction* out = outp;
    CHECK(lmcp_unpack_VehicleAction(inb, size_remain, &(out->super)))
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
size_t lmcp_pack_StopMovementAction(uint8_t* buf, StopMovementAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_VehicleAction(outb, &(i->super));
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

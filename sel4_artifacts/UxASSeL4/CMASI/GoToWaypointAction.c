
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "GoToWaypointAction.h"
#include "NavigationAction.h"
void lmcp_pp_GoToWaypointAction(GoToWaypointAction* s) {
    printf("GoToWaypointAction{");
    printf("Inherited from NavigationAction:\n");
    lmcp_pp_NavigationAction(&(s->super));
    printf("WaypointNumber: ");
    printf("%lld",s->WaypointNumber);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_GoToWaypointAction (GoToWaypointAction* i) {
    size_t out = 0;
    out += lmcp_packsize_NavigationAction(&(i->super));
    out += sizeof(int64_t);
    return out;
}
size_t lmcp_pack_GoToWaypointAction_header(uint8_t* buf, GoToWaypointAction* i) {
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
    outb += lmcp_pack_uint32_t(outb, 28);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_GoToWaypointAction(GoToWaypointAction* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_NavigationAction(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_GoToWaypointAction (GoToWaypointAction** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(GoToWaypointAction));
    ((lmcp_object*)(*i)) -> type = 28;
}
int lmcp_unpack_GoToWaypointAction(uint8_t** inb, size_t *size_remain, GoToWaypointAction* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    GoToWaypointAction* out = outp;
    CHECK(lmcp_unpack_NavigationAction(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->WaypointNumber)))
    return 0;
}
size_t lmcp_pack_GoToWaypointAction(uint8_t* buf, GoToWaypointAction* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_NavigationAction(outb, &(i->super));
    outb += lmcp_pack_int64_t(outb, i->WaypointNumber);
    return (outb - buf);
}

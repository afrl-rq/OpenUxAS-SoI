
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "PathWaypoint.h"
#include "Waypoint.h"
void lmcp_pp_PathWaypoint(PathWaypoint* s) {
    printf("PathWaypoint{");
    printf("Inherited from Waypoint:\n");
    lmcp_pp_Waypoint(&(s->super));
    printf("PauseTime: ");
    printf("%lld",s->PauseTime);
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_PathWaypoint (PathWaypoint* i) {
    size_t out = 0;
    out += lmcp_packsize_Waypoint(&(i->super));
    out += sizeof(int64_t);
    return out;
}
size_t lmcp_pack_PathWaypoint_header(uint8_t* buf, PathWaypoint* i) {
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
    outb += lmcp_pack_uint32_t(outb, 57);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_PathWaypoint(PathWaypoint* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_Waypoint(&(out->super), 0);
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_PathWaypoint (PathWaypoint** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(PathWaypoint));
    ((lmcp_object*)(*i)) -> type = 57;
}
int lmcp_unpack_PathWaypoint(uint8_t** inb, size_t *size_remain, PathWaypoint* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    PathWaypoint* out = outp;
    CHECK(lmcp_unpack_Waypoint(inb, size_remain, &(out->super)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->PauseTime)))
    return 0;
}
size_t lmcp_pack_PathWaypoint(uint8_t* buf, PathWaypoint* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_Waypoint(outb, &(i->super));
    outb += lmcp_pack_int64_t(outb, i->PauseTime);
    return (outb - buf);
}


#include "common/struct_defines.h"
#include "common/conv.h"
#include "EntityState.h"
#include "Location3D.h"
#include "PayloadState.h"
#include "enums.h"
#include "KeyValuePair.h"
void lmcp_pp_EntityState(EntityState* s) {
    printf("EntityState{");
    printf("id: ");
    printf("%lld",s->id);
    printf("\n");
    printf("u: ");
    printf("%u",s->u);
    printf("\n");
    printf("v: ");
    printf("%u",s->v);
    printf("\n");
    printf("w: ");
    printf("%u",s->w);
    printf("\n");
    printf("udot: ");
    printf("%u",s->udot);
    printf("\n");
    printf("vdot: ");
    printf("%u",s->vdot);
    printf("\n");
    printf("wdot: ");
    printf("%u",s->wdot);
    printf("\n");
    printf("heading: ");
    printf("%u",s->heading);
    printf("\n");
    printf("pitch: ");
    printf("%u",s->pitch);
    printf("\n");
    printf("roll: ");
    printf("%u",s->roll);
    printf("\n");
    printf("p: ");
    printf("%u",s->p);
    printf("\n");
    printf("q: ");
    printf("%u",s->q);
    printf("\n");
    printf("r: ");
    printf("%u",s->r);
    printf("\n");
    printf("course: ");
    printf("%u",s->course);
    printf("\n");
    printf("groundspeed: ");
    printf("%u",s->groundspeed);
    printf("\n");
    printf("location: ");
    lmcp_pp_Location3D((s->location));
    printf("\n");
    printf("energyavailable: ");
    printf("%u",s->energyavailable);
    printf("\n");
    printf("actualenergyrate: ");
    printf("%u",s->actualenergyrate);
    printf("\n");
    printf("payloadstatelist: ");
    printf("[");
    for (uint32_t index = 0; index < s->payloadstatelist_ai.length; index++) {
        lmcp_pp_PayloadState((s->payloadstatelist[index]));
        printf(",");
    }
    printf("\n");
    printf("currentwaypoint: ");
    printf("%lld",s->currentwaypoint);
    printf("\n");
    printf("currentcommand: ");
    printf("%lld",s->currentcommand);
    printf("\n");
    printf("mode: ");
    printf("%i", s->mode);
    printf("\n");
    printf("associatedtasks: ");
    printf("[");
    for (uint32_t index = 0; index < s->associatedtasks_ai.length; index++) {
        printf("%lld",s->associatedtasks[index]);
        printf(",");
    }
    printf("\n");
    printf("time: ");
    printf("%lld",s->time);
    printf("\n");
    printf("info: ");
    printf("[");
    for (uint32_t index = 0; index < s->info_ai.length; index++) {
        lmcp_pp_KeyValuePair((s->info[index]));
        printf(",");
    }
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_EntityState (EntityState* i) {
    size_t out = 0;
    out += sizeof(int64_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    if (i->location==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_Location3D(i->location);
    }
    out += sizeof(uint32_t);
    out += sizeof(uint32_t);
    out += 2;
    for (uint32_t index = 0; index < i->payloadstatelist_ai.length; index++) {
        out += 15 + lmcp_packsize_PayloadState(i->payloadstatelist[index]);
    }
    out += sizeof(int64_t);
    out += sizeof(int64_t);
    out += 4;
    out += 2;
    for (uint32_t index = 0; index < i->associatedtasks_ai.length; index++) {
        out += sizeof(int64_t);
    }
    out += sizeof(int64_t);
    out += 2;
    for (uint32_t index = 0; index < i->info_ai.length; index++) {
        out += 15 + lmcp_packsize_KeyValuePair(i->info[index]);
    }
    return out;
}
size_t lmcp_pack_EntityState_header(uint8_t* buf, EntityState* i) {
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
    outb += lmcp_pack_uint32_t(outb, 14);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_EntityState(EntityState* out, int out_malloced) {
    if (out == NULL)
        return;
    if (out->location != NULL) {
        lmcp_free_Location3D(out->location, 1);
    }
    if (out->payloadstatelist != NULL) {
        for (uint32_t index = 0; index < out->payloadstatelist_ai.length; index++) {
            if (out->payloadstatelist[index] != NULL) {
                lmcp_free_PayloadState(out->payloadstatelist[index], 1);
            }
        }
        free(out->payloadstatelist);
    }
    if (out->associatedtasks != NULL) {
        free(out->associatedtasks);
    }
    if (out->info != NULL) {
        for (uint32_t index = 0; index < out->info_ai.length; index++) {
            if (out->info[index] != NULL) {
                lmcp_free_KeyValuePair(out->info[index], 1);
            }
        }
        free(out->info);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_EntityState (EntityState** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(EntityState));
    ((lmcp_object*)(*i)) -> type = 14;
}
int lmcp_unpack_EntityState(uint8_t** inb, size_t *size_remain, EntityState* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    EntityState* out = outp;
    uint32_t tmp;
    uint16_t tmp16;
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->id)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->u)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->v)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->w)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->udot)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->vdot)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->wdot)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->heading)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->pitch)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->roll)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->p)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->q)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->r)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->course)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->groundspeed)))
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->location = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_Location3D(&(out->location));
        CHECK(lmcp_unpack_Location3D(inb, size_remain, (out->location)))
    }
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->energyavailable)))
    CHECK(lmcp_unpack_uint32_t(inb, size_remain, &(out->actualenergyrate)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->payloadstatelist = malloc(sizeof(PayloadState*) * tmp);
    if (out->payloadstatelist==0) {
        return -1;
    }
    out->payloadstatelist_ai.length = tmp;
    for (uint32_t index = 0; index < out->payloadstatelist_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->payloadstatelist[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_PayloadState(&(out->payloadstatelist[index]));
            CHECK(lmcp_unpack_PayloadState(inb, size_remain, (out->payloadstatelist[index])))
        }
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->currentwaypoint)))
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->currentcommand)))
    CHECK(lmcp_unpack_int32_t(inb, size_remain, (int*) &(out->mode)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->associatedtasks = malloc(sizeof(int64_t*) * tmp);
    if (out->associatedtasks==0) {
        return -1;
    }
    out->associatedtasks_ai.length = tmp;
    for (uint32_t index = 0; index < out->associatedtasks_ai.length; index++) {
        CHECK(lmcp_unpack_int64_t(inb, size_remain, &out->associatedtasks[index]))
    }
    CHECK(lmcp_unpack_int64_t(inb, size_remain, &(out->time)))
    CHECK(lmcp_unpack_uint16_t(inb, size_remain, &tmp16))
    tmp = tmp16;
    (out)->info = malloc(sizeof(KeyValuePair*) * tmp);
    if (out->info==0) {
        return -1;
    }
    out->info_ai.length = tmp;
    for (uint32_t index = 0; index < out->info_ai.length; index++) {
        uint8_t isnull;
        uint32_t objtype;
        uint16_t objseries;
        char seriesname[8];
        CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
        if (isnull == 0 && inb != NULL) {
            out->info[index] = NULL;
        } else if (inb != NULL) {
            CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
            CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
            CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
            lmcp_init_KeyValuePair(&(out->info[index]));
            CHECK(lmcp_unpack_KeyValuePair(inb, size_remain, (out->info[index])))
        }
    }
    return 0;
}
size_t lmcp_pack_EntityState(uint8_t* buf, EntityState* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_int64_t(outb, i->id);
    outb += lmcp_pack_uint32_t(outb, i->u);
    outb += lmcp_pack_uint32_t(outb, i->v);
    outb += lmcp_pack_uint32_t(outb, i->w);
    outb += lmcp_pack_uint32_t(outb, i->udot);
    outb += lmcp_pack_uint32_t(outb, i->vdot);
    outb += lmcp_pack_uint32_t(outb, i->wdot);
    outb += lmcp_pack_uint32_t(outb, i->heading);
    outb += lmcp_pack_uint32_t(outb, i->pitch);
    outb += lmcp_pack_uint32_t(outb, i->roll);
    outb += lmcp_pack_uint32_t(outb, i->p);
    outb += lmcp_pack_uint32_t(outb, i->q);
    outb += lmcp_pack_uint32_t(outb, i->r);
    outb += lmcp_pack_uint32_t(outb, i->course);
    outb += lmcp_pack_uint32_t(outb, i->groundspeed);
    if (i->location==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 3);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_Location3D(outb, i->location);
    }
    outb += lmcp_pack_uint32_t(outb, i->energyavailable);
    outb += lmcp_pack_uint32_t(outb, i->actualenergyrate);
    outb += lmcp_pack_uint16_t(outb, i->payloadstatelist_ai.length);
    for (uint32_t index = 0; index < i->payloadstatelist_ai.length; index++) {
        if (i->payloadstatelist[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 6);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_PayloadState(outb, i->payloadstatelist[index]);
        }
    }
    outb += lmcp_pack_int64_t(outb, i->currentwaypoint);
    outb += lmcp_pack_int64_t(outb, i->currentcommand);
    outb += lmcp_pack_int32_t(outb, (int) i->mode);
    outb += lmcp_pack_uint16_t(outb, i->associatedtasks_ai.length);
    for (uint32_t index = 0; index < i->associatedtasks_ai.length; index++) {
        outb += lmcp_pack_int64_t(outb, i->associatedtasks[index]);
    }
    outb += lmcp_pack_int64_t(outb, i->time);
    outb += lmcp_pack_uint16_t(outb, i->info_ai.length);
    for (uint32_t index = 0; index < i->info_ai.length; index++) {
        if (i->info[index]==NULL) {
            outb += lmcp_pack_uint8_t(outb, 0);
        } else {
            outb += lmcp_pack_uint8_t(outb, 1);
            memcpy(outb, "CMASI", 5);
            outb += 5;
            for (size_t j = 5; j < 8; j++, outb++)
                *outb = 0;
            outb += lmcp_pack_uint32_t(outb, 2);
            outb += lmcp_pack_uint16_t(outb, 3);
            outb += lmcp_pack_KeyValuePair(outb, i->info[index]);
        }
    }
    return (outb - buf);
}

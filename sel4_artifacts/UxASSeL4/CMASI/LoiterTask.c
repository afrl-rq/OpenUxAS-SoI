
#include <stdlib.h>
#include <inttypes.h>
#include "common/struct_defines.h"
#include "common/conv.h"
#include "LoiterTask.h"
#include "Task.h"
#include "LoiterAction.h"
void lmcp_pp_LoiterTask(LoiterTask* s) {
    printf("LoiterTask{");
    printf("Inherited from Task:\n");
    lmcp_pp_Task(&(s->super));
    printf("DesiredAction: ");
    lmcp_pp_LoiterAction((s->DesiredAction));
    printf("\n");
    printf("}");
}
size_t lmcp_packsize_LoiterTask (LoiterTask* i) {
    size_t out = 0;
    out += lmcp_packsize_Task(&(i->super));
    if (i->DesiredAction==NULL) {
        out += 1;
    } else {
        out += 15 + lmcp_packsize_LoiterAction(i->DesiredAction);
    }
    return out;
}
size_t lmcp_pack_LoiterTask_header(uint8_t* buf, LoiterTask* i) {
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
    outb += lmcp_pack_uint32_t(outb, 34);
    outb += lmcp_pack_uint16_t(outb, 3);
    return 15;
}
void lmcp_free_LoiterTask(LoiterTask* out, int out_malloced) {
    if (out == NULL)
        return;
    lmcp_free_Task(&(out->super), 0);
    if (out->DesiredAction != NULL) {
        lmcp_free_LoiterAction(out->DesiredAction, 1);
    }
    if (out_malloced == 1) {
        free(out);
    }
}
void lmcp_init_LoiterTask (LoiterTask** i) {
    if (i == NULL) return;
    (*i) = calloc(1,sizeof(LoiterTask));
    ((lmcp_object*)(*i)) -> type = 34;
}
int lmcp_unpack_LoiterTask(uint8_t** inb, size_t *size_remain, LoiterTask* outp) {
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if (size_remain == NULL || *size_remain == 0) {
        return -1;
    }
    LoiterTask* out = outp;
    CHECK(lmcp_unpack_Task(inb, size_remain, &(out->super)))
    uint8_t isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    CHECK(lmcp_unpack_uint8_t(inb, size_remain, &isnull))
    if (isnull == 0 && inb != NULL) {
        out->DesiredAction = NULL;
    } else if (inb != NULL) {
        CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname))
        CHECK(lmcp_unpack_uint32_t(inb, size_remain, &objtype))
        CHECK(lmcp_unpack_uint16_t(inb, size_remain, &objseries))
        lmcp_init_LoiterAction(&(out->DesiredAction));
        CHECK(lmcp_unpack_LoiterAction(inb, size_remain, (out->DesiredAction)))
    }
    return 0;
}
size_t lmcp_pack_LoiterTask(uint8_t* buf, LoiterTask* i) {
    if (i == NULL) return 0;
    uint8_t* outb = buf;
    outb += lmcp_pack_Task(outb, &(i->super));
    if (i->DesiredAction==NULL) {
        outb += lmcp_pack_uint8_t(outb, 0);
    } else {
        outb += lmcp_pack_uint8_t(outb, 1);
        memcpy(outb, "CMASI", 5);
        outb += 5;
        for (size_t j = 5; j < 8; j++, outb++)
            *outb = 0;
        outb += lmcp_pack_uint32_t(outb, 33);
        outb += lmcp_pack_uint16_t(outb, 3);
        outb += lmcp_pack_LoiterAction(outb, i->DesiredAction);
    }
    return (outb - buf);
}

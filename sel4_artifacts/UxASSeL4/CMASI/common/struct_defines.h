#pragma once
#include "types.h"

struct lmcp_object_struct {
    uint32_t type;
    // series name, version can also go here
};

typedef struct lmcp_object_struct lmcp_object;


struct array_info_struct {
    uint32_t length;
};
typedef struct array_info_struct array_info;

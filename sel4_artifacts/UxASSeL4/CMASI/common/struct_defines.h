#pragma once
#include <stdint.h>
#include <stdlib.h>

typedef struct {
    uint32_t type;
    // series name, version can also go here
} lmcp_object;


typedef struct {
    uint32_t length;
} array_info;

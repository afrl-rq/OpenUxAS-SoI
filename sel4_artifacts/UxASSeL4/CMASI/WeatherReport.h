
#pragma once
#include "common/struct_defines.h"
#include "common/conv.h"
#include "AbstractZone.h"
#define LMCP_WeatherReport_SUB "afrl.cmasi.WeatherReport"

#define LMCP_WeatherReport_TYPENAME "WeatherReport"

#define LMCP_WeatherReport_TYPE 55

struct WeatherReport_struct {
    lmcp_object super;
    AbstractZone* area;

// Units: meter/sec
    uint32_t windspeed;

// Units: degree
    uint32_t winddirection;

// Units: meter
    uint32_t visibility;

// Units: meter
    uint32_t cloudceiling;

    uint32_t cloudcoverage;

};
typedef struct WeatherReport_struct WeatherReport;
void lmcp_pp_WeatherReport(WeatherReport* s);
size_t lmcp_packsize_WeatherReport (WeatherReport* i);
size_t lmcp_pack_WeatherReport_header(uint8_t* buf, WeatherReport* i);
void lmcp_free_WeatherReport(WeatherReport* i, int out_malloced);
void lmcp_init_WeatherReport (WeatherReport** i);
int lmcp_unpack_WeatherReport(uint8_t** buf, size_t *size_remain,WeatherReport* outp);
size_t lmcp_pack_WeatherReport(uint8_t* buf, WeatherReport* i);

#pragma once
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include "conv.h"
// from beej

#define LMCP_DEBUG(fmt,args...) \
  printf("%s,%s,%i:"fmt,__FUNCTION__,__FILE__,__LINE__,##args)

#define CHECK(i) { if(i == -1) { LMCP_DEBUG("Check failed!\n"); return -1; } }



size_t lmcp_pack_uint16_t (uint8_t* buf, uint16_t in) ;

int lmcp_unpack_uint16_t (uint8_t** buf, size_t *size_remain, uint16_t *out) ;

int lmcp_unpack_uint32_t(uint8_t **buf, size_t * size_remain, uint32_t *out);
size_t lmcp_pack_uint32_t(uint8_t *buf, uint32_t i);

size_t lmcp_pack_uint64_t (uint8_t *buf, uint64_t i) ;


int lmcp_unpack_uint64_t(uint8_t **buf, size_t * size_remain, uint64_t *out);


size_t lmcp_pack_int16_t (uint8_t* buf, int8_t in) ;

size_t lmcp_pack_int32_t (uint8_t* buf, int32_t in) ;
size_t lmcp_pack_int64_t (uint8_t* buf, int64_t in) ;

int lmcp_unpack_int16_t (uint8_t** buf, size_t * size_remain, int16_t* out) ;
int lmcp_unpack_int32_t (uint8_t** buf, size_t * size_remain, int32_t* out) ;
int lmcp_unpack_int64_t (uint8_t** buf, size_t * size_remain, int64_t* out) ;

int lmcp_unpack_8byte (uint8_t** buf, size_t * size_remain, char* out);
int lmcp_unpack_4byte (uint8_t** buf, size_t * size_remain, char* out);
//
size_t lmcp_pack_float(uint8_t* buf, float in) ;

int lmcp_unpack_float(uint8_t** buf, size_t * size_remain, float* out) ;

size_t lmcp_pack_double(uint8_t* buf, double in) ;

int lmcp_unpack_double(uint8_t** buf, size_t * size_remain, double* out) ;

size_t lmcp_pack_uint8_t(uint8_t* buf, uint8_t in) ;

int lmcp_unpack_uint8_t(uint8_t** buf, size_t * size_remain, uint8_t* out) ;

int lmcp_unpack_char(uint8_t** buf, size_t * size_remain, char* out) ;

size_t lmcp_pack_char(uint8_t* buf, char in) ;



int lmcp_unpack_structheader(uint8_t** inb, size_t* size_remain, char* seriesname, uint32_t* objtype, uint16_t* objseries);

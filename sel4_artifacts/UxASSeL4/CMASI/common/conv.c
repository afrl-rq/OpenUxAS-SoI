#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "conv.h"
// from beej
//

#define INPUT_SANITY                                        \
  if (buf == NULL || *buf == NULL || size_remain == NULL) { \
    LMCP_DEBUG("Fail.\n");                                  \
    LMCP_DEBUG("buf == 0x%p\n",buf);                        \
    LMCP_DEBUG("*buf == 0x%p\n",*buf);                      \
    LMCP_DEBUG("size_remain == 0x%p\n",size_remain);        \
    return -1;                                              \
  }


#define SIZE_SANITY(x)                          \
  if (*size_remain < x) {                       \
    LMCP_DEBUG("Failed *size_remain(%zu) < %u\n",*size_remain,x);  \
    return -1;                                  \
  }

int lmcp_unpack_8byte (uint8_t** buf, size_t * size_remain, char* out) {
  INPUT_SANITY;
  SIZE_SANITY(8);
  out[0] = (*buf)[0];
  out[1] = (*buf)[1];
  out[2] = (*buf)[2];
  out[3] = (*buf)[3];
  out[4] = (*buf)[4];
  out[5] = (*buf)[5];
  out[6] = (*buf)[6];
  out[7] = (*buf)[7];
  *buf += 8;
  *size_remain -= 8;
  return 0;
}

int lmcp_unpack_4byte (uint8_t** buf, size_t * size_remain, char* out) {
  INPUT_SANITY;
  SIZE_SANITY(4);
  out[0] = (*buf)[0];
  out[1] = (*buf)[1];
  out[2] = (*buf)[2];
  out[3] = (*buf)[3];
  *buf += 4;
  *size_remain -= 4;
  return 0;
}

size_t lmcp_pack_uint16_t (uint8_t* buf, uint16_t in) {
  buf[0] = in >> 8;
  buf[1] = in;
  return 2;
}

int lmcp_unpack_uint16_t (uint8_t** buf, size_t *size_remain, uint16_t* out) {
  INPUT_SANITY;
  SIZE_SANITY(2);
  *out = ((*buf)[0] << 8) | (*buf)[1];
  *buf += 2;
  *size_remain -= 2;
  return 0;
}

int lmcp_unpack_uint32_t (uint8_t **buf, size_t *size_remain, uint32_t* out)
{
  INPUT_SANITY;
  SIZE_SANITY(4);
	*out = ((*buf)[0]<<24) | ((*buf)[1]<<16) | ((*buf)[2]<<8) | (*buf)[3];
  *buf += 4;
  *size_remain -= 4;
  return 0;
}

size_t lmcp_pack_uint32_t (uint8_t *buf, uint32_t i)
{
  buf[0] = i>>24;
  buf[1] = i>>16;
  buf[2] = i>>8;
  buf[3] = i;
  return 4;
}

size_t lmcp_pack_uint64_t (uint8_t *buf, uint64_t i) {
  buf[0] = i >> 56;
  buf[1] = i >> 48;
  buf[2] = i >> 40;
  buf[3] = i >> 32;
  buf[4] = i >> 24;
  buf[5] = i >> 16;
  buf[6] = i >> 8;
  buf[7] = i;
  return 8;
}


int lmcp_unpack_uint64_t (uint8_t **buf, size_t *size_remain, uint64_t* out)
{
  INPUT_SANITY;
  SIZE_SANITY(8);
	*out =
    ((uint64_t)((*buf)[0])<<56)
    | ((uint64_t)((*buf)[1])<<48)
    | ((uint64_t)((*buf)[2])<<40)
    | ((uint64_t)((*buf)[3])<<32)
    | ((uint64_t)((*buf)[4])<<24)
    | ((uint64_t)((*buf)[5])<<16)
    | ((uint64_t)((*buf)[6])<<8)
    | ((uint64_t)((*buf)[7]));
  *buf += 8;
  *size_remain -= 8;
  return 0;
}


size_t lmcp_pack_int8_t (uint8_t* buf, int8_t in) {
  lmcp_pack_uint8_t(buf, *(uint8_t*)&in);
  return 1;
}

size_t lmcp_pack_int32_t (uint8_t* buf, int32_t in) {
  lmcp_pack_uint32_t(buf, *(uint32_t*)&in);
  return 4;
}
size_t lmcp_pack_int64_t (uint8_t* buf, int64_t in) {
  lmcp_pack_uint64_t(buf, *(uint64_t*)&in);
  return 8;
}

int lmcp_unpack_int16_t (uint8_t** buf, size_t *size_remain, int16_t* out) {
  int16_t j;
  CHECK(lmcp_unpack_uint16_t(buf, size_remain, (uint16_t*)&j));
  if (buf != NULL && *buf != NULL) {
    *out = *(int16_t*)&j;
    return 0;
  }
  return -1;
}
int lmcp_unpack_int32_t (uint8_t** buf, size_t *size_remain, int32_t* out) {
  int32_t j;
  CHECK(lmcp_unpack_uint32_t(buf, size_remain, (uint32_t*)&j));
  if (buf != NULL && *buf != NULL) {
    *out= *(int32_t*)&j;
    return 0;
  }
  return -1;
}
int lmcp_unpack_int64_t (uint8_t** buf, size_t *size_remain, int64_t* out) {
  int64_t j;
  CHECK(lmcp_unpack_uint64_t(buf,size_remain,(uint64_t*)&j));
  if (buf != NULL && *buf != NULL) {
    *out = *(int64_t*)&j;
    return 0;
  }
  return -1;
}
// from beej guide
// macros for packing floats and doubles:
#define pack754_32(f) (pack754((f), 32, 8))
#define pack754_64(f) (pack754((f), 64, 11))
#define unpack754_32(i) (unpack754((i), 32, 8))
#define unpack754_64(i) (unpack754((i), 64, 11))


// pack754() -- pack a floating point number into IEEE-754 format
 
long long pack754(long double f, unsigned bits, unsigned expbits)
{
	long double fnorm;
	int shift;
	long long sign, exp, significand;
	unsigned significandbits = bits - expbits - 1; // -1 for sign bit

	if (f == 0.0) return 0; // get this special case out of the way

	// check sign and begin normalization
	if (f < 0) { sign = 1; fnorm = -f; }
	else { sign = 0; fnorm = f; }

	// get the normalized form of f and track the exponent
	shift = 0;
	while(fnorm >= 2.0) { fnorm /= 2.0; shift++; }
	while(fnorm < 1.0) { fnorm *= 2.0; shift--; }
	fnorm = fnorm - 1.0;

	// calculate the binary form (non-float) of the significand data
	significand = fnorm * ((1LL<<significandbits) + 0.5f);

	// get the biased exponent
	exp = shift + ((1<<(expbits-1)) - 1); // shift + bias

	// return the final answer
	return (sign<<(bits-1)) | (exp<<(bits-expbits-1)) | significand;
}


// unpack754() -- unpack a floating point number from IEEE-754 format
 
long double unpack754(long long i, unsigned bits, unsigned expbits)
{
	long double result;
	long long shift;
	unsigned bias;
	unsigned significandbits = bits - expbits - 1; // -1 for sign bit

	if (i == 0) return 0.0;

	// pull the significand
	result = (i&((1LL<<significandbits)-1)); // mask
	result /= (1LL<<significandbits); // convert back to float
	result += 1.0f; // add the one back on

	// deal with the exponent
	bias = (1<<(expbits-1)) - 1;
	shift = ((i>>significandbits)&((1LL<<expbits)-1)) - bias;
	while(shift > 0) { result *= 2.0; shift--; }
	while(shift < 0) { result /= 2.0; shift++; }

	// sign it
	result *= (i>>(bits-1))&1? -1.0: 1.0;

	return result;
}

size_t lmcp_pack_float(uint8_t* buf, float in) {
  uint32_t l = pack754_32(in);
  lmcp_pack_uint32_t(buf, l);
  return 4;
}

int lmcp_unpack_float(uint8_t** buf, size_t* size_remain, float* out) {
  uint32_t p;  int res = lmcp_unpack_uint32_t(buf, size_remain, &p);
  if (buf != NULL && *buf != NULL && res == 0) {
    *out = (float) unpack754_32(p);
    return 0;
  }
  else
    return -1;
}

size_t lmcp_pack_double(uint8_t* buf, double in) {
  uint64_t l = pack754_64(in);
  lmcp_pack_uint64_t(buf, l);
  return 8;
}

int lmcp_unpack_double(uint8_t** buf, size_t* size_remain, double* out) {
  uint64_t p; int res = lmcp_unpack_uint64_t(buf, size_remain, &p);
  if (buf != NULL && *buf != NULL && res == 0) {
    *out = (double) unpack754_64(p);
    return 0;
  }
  else
    return -1;
} 

size_t lmcp_pack_uint8_t(uint8_t* buf, uint8_t in) {
  *buf = in;
  return 1;
}

int lmcp_unpack_uint8_t(uint8_t** buf, size_t *size_remain, uint8_t* out) {
  if (buf == NULL || *buf == NULL || size_remain == NULL) {
    return -1;
  }
  if (*size_remain < 1) {
    return -1;
  }
  *out = **buf;
  *buf += 1;
  *size_remain -= 1;
  return 0;
}

int lmcp_unpack_char(uint8_t** buf, size_t *size_remain, char* out) {
  if (buf == NULL || *buf == NULL || size_remain == NULL) {
    return -1;
  }
  if (*size_remain < 1) {
    return -1;
  }
  *out = **buf;
  *buf += 1;
  *size_remain -= 1;
  return 0;
}

size_t lmcp_pack_char(uint8_t* buf, char in) {
  *buf = in;
  return 1;
}


int lmcp_unpack_structheader(uint8_t** inb, size_t* size_remain, char* seriesname, uint32_t* objtype, uint16_t* objseries) {
  uint8_t isnull = 0;
  lmcp_unpack_uint8_t(inb, size_remain, &isnull);
  if (inb == NULL || *inb == NULL || isnull == 0) {
    return -1;
  }
  CHECK(lmcp_unpack_8byte(inb, size_remain, seriesname));
  CHECK(lmcp_unpack_uint32_t(inb, size_remain, objtype));
  CHECK(lmcp_unpack_uint16_t(inb, size_remain, objseries));
  return 0;
}

#ifndef __MCUTILS_H__
#define __MCUTILS_H__
#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>

#define WP_HDR_LEN 15

#define MC_SZ(waypoints) (sizeof(mc_t)-(MAX_WAYPOINTS*sizeof(wp_t))+(waypoints*sizeof(wp_t)))

#define BSWAP(E) (sizeof(E) == 8 ? E = __builtin_bswap64(E) :\
                  (sizeof(E) == 4 ? E = __builtin_bswap32(E) :\
                   (sizeof(E) == 2 ? E = __builtin_bswap16(E) :\
                    assert(false))))

struct  __attribute__((packed)) wp_struct {
  char header[WP_HDR_LEN];
  uint64_t /*double*/ latitude;
  uint64_t /*double*/ longitude;
  uint32_t /*float*/ altitude;
  int32_t altitude_type;
  uint64_t id;
  uint64_t nxid;
  uint32_t /*float*/ speed;
  int32_t speed_type;
  float climbrate;
  int32_t turntype;
  uint16_t vehicleactionlistsize;
  uint64_t contingencywaypointa;
  uint64_t contingencywaypointb;
  uint16_t associatedtasksize;
};

typedef struct wp_struct wp_t;

#define MC_HDR_LEN 23
 
struct __attribute__((packed)) mc_trnc_struct {
  char header[MC_HDR_LEN];
  uint64_t commandid;
  uint64_t vehicleid;
  uint16_t vehicleactionlistsize;
  int32_t commandstatus;
  uint16_t waypointssize;
};

typedef struct mc_trnc_struct mc_trnc_t;

#define MAX_WAYPOINTS 255

struct __attribute__((packed)) mc_full_struct {
  char header[MC_HDR_LEN];
  uint64_t commandid;
  uint64_t vehicleid;
  uint16_t vehicleactionlistsize;
  int32_t commandstatus;
  uint16_t waypointssize;
  wp_t waypoints[MAX_WAYPOINTS];
  uint64_t startingwaypoint;
  uint32_t checksum;
};

typedef struct mc_full_struct mc_full_t;

union mc_union {
  mc_trnc_t trnc;
  mc_full_t full;
};

typedef union mc_union mc_t;

bool DeserializeMCFromBuffer(const uint8_t * buf, mc_t * mc_ptr);

bool DeserializeMCFromFile(FILE * f, mc_t * mc_ptr);

void PrintMC(FILE * f, mc_t * mc_ptr);

bool MCPrefix(const mc_t * orig_mc_ptr,
              const uint64_t id,
              const uint16_t len,
              mc_t * mc_new_ptr);

void UnFixCopiedMC(mc_t * mc_ptr);

#endif /* __MCUTILS_H__ */

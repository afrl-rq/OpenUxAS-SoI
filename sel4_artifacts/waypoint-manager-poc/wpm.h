#ifndef __WPM_H__
#define __WPM_H__
#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>

#define MKSWAPDECL(N) void swap##N(void *v)

MKSWAPDECL(2);

MKSWAPDECL(4);

MKSWAPDECL(8);


struct  __attribute__((packed)) wp_struct {
  char header[15];
  /** Latitude */
  /* double __Latitude; */
  double latitude;
  /** Longitude */
  /* double __Longitude; */
  double longitude;
  /** Altitude for this waypoint */
  /* float __Altitude; */
  float altitude;
  /** Altitude type for specified altitude */
  /* afrl::cmasi::AltitudeType::AltitudeType __AltitudeType; */
  int32_t altitude_type;
  /** A unique waypoint number */
  /* int64_t __Number; */
  uint64_t id;
  /** The index of the next waypoint in the list. Consecutively
      numbered waypoints are <b>not</b> considered linked, the link
      must be explicitly stated in this field. */
  /* int64_t __NextWaypoint; */
  uint64_t nxid;
  /** Commanded speed for this waypoint. See SpeedType for defintion of this field. */
  /* float __Speed; */
  float speed;
  /** Type of commanded speed */
  /* afrl::cmasi::SpeedType::SpeedType __SpeedType; */
  int32_t speed_type;
  /** The commanded climb rate. Positive values upwards. For surface (ground and sea) entities, this value is ignored. */
  /* float __ClimbRate; */
  float climbrate;
  /** The type of turn to execute */
  /* afrl::cmasi::TurnType::TurnType __TurnType; */
  int32_t turntype;
  /** A list of actions to perform at this waypoint */
  /* std::vector< afrl::cmasi::VehicleAction* > __VehicleActionList; */
  /* NB: This is here to make serialization/deserialization
     easier. LCMP will serialize vectors by prefixing the size as a
     unsigned 16-bit integer.*/
  uint16_t vehicleactionlistsize;
  /** A waypoint for contingency (e.g. lost-comm, alternate mission)
      operations. A value of zero denotes that no contingency point is
      specified. */
  /* int64_t __ContingencyWaypointA; */
  uint64_t contingencywaypointa;
  /** A waypoint for contingency (e.g. lost-comm, alternate
      mission) operations. A value of zero denotes that no
      contingency point is specified. */
  /* int64_t __ContingencyWaypointB; */
  uint64_t contingencywaypointb;
  /** A list of tasks that are associated with this waypoint. A length
      of zero denotes no associated tasks. This field is for analysis
      purposes. The automation service should associate a list of tasks with
      each waypoint to enable analysis of the allocation of tasks to
      vehicles. */
  /* std::vector< int64_t > __AssociatedTasks; */
  uint16_t associatedtasksize;
};

typedef struct wp_struct wp_t;

struct __attribute__((packed)) mc_trnc_struct {
  char header[23];
  uint64_t commandid;
  uint64_t vehicleid;
  uint16_t vehicleactionlistsize;
  int32_t commandstatus;
  uint16_t waypointssize;
};

typedef struct mc_trnc_struct mc_trnc_t;

struct __attribute__((packed)) mc_full_struct {
  char header[23];
  uint64_t commandid;
  uint64_t vehicleid;
  uint16_t vehicleactionlistsize;
  int32_t commandstatus;
  uint16_t waypointssize;
  wp_t waypoints[65535];
  uint64_t startingwaypoint;
  uint32_t checksum;
};

typedef struct mc_full_struct mc_full_t;

union mc_union {
  mc_trnc_t trnc;
  mc_full_t full;
};

typedef union mc_union mc_t;


bool deserialize_mc(FILE * f, mc_t * mc);

bool correct_mc(mc_t * mc);

void output_mc(FILE * f, mc_t * mc);

uint32_t calculateChecksum(const uint8_t * bytes, const uint32_t len);

bool sub_mc(const mc_t * super, const uint64_t const nxid, uint16_t len, mc_t * sub);

bool find_wp(const mc_t * mc, const uint64_t nxid, wp_t * wp);


#endif /* __WPM_H__ */

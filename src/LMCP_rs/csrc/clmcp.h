// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
 * File:   clmcp.h
 * Author: acfoltzer
 *
 * Temporary, hand-written translations of the MDMs needed to run Rust examples
 */

#include <stdbool.h>
#include <stdint.h>

typedef enum {
  AltitudeType_AGL,
  AltitudeType_MSL,
} AltitudeType;

typedef enum {
  CommandStatusType_Pending,
  CommandStatusType_Approved,
  CommandStatusType_InProcess,
  CommandStatusType_Executed,
} CommandStatusType;

typedef enum {
  LoiterType_VehicleDefault = 0,
  LoiterType_Circular = 1,
  LoiterType_Racetrack = 2,
  LoiterType_FigureEight = 3,
  LoiterType_Hover = 4,
} LoiterType;

typedef enum {
  NavigationMode_Waypoint = 0,
  NavigationMode_Loiter = 1,
  NavigationMode_FlightDirector = 2,
  NavigationMode_TargetTrack = 3,
  NavigationMode_FollowLeader = 4,
  NavigationMode_LostComm = 5,
} NavigationMode;

typedef enum {
  SpeedType_Airspeed = 0,
  SpeedType_Groundspeed = 1,
} SpeedType;

typedef enum {
  TurnType_TurnShort = 0,
  TurnType_FlyOver = 1,
} TurnType;

typedef enum {
  WavelengthBand_AllAny = 0,
  WavelengthBand_EO = 1,
  WavelengthBand_LWIR = 2,
  WavelengthBand_SWIR = 3,
  WavelengthBand_MWIR = 4,
  WavelengthBand_Other = 5,
} WavelengthBand;

typedef struct {
  const char* key;
  const char* value;
} KeyValuePair;

typedef struct {
  int64_t payload_id;
  const char* payload_kind;
  KeyValuePair* parameters;
  size_t parameters_len;
} PayloadConfiguration;

typedef struct {
  int64_t id;
  const char* affiliation;
  const char* entity_type;
  const char* label;
  float nominal_speed;
  float nominal_altitude;
  AltitudeType nominal_altitude_type;
  PayloadConfiguration* payload_configuration_list;
  size_t payload_configuration_list_len;
  KeyValuePair* info;
  size_t info_len;
} EntityConfiguration;

typedef struct {
  const char* name;
  float airspeed;
  float pitch_angle;
  float vertical_speed;
  float max_bank_angle;
  float energy_rate;
} FlightProfile;

typedef struct {
  EntityConfiguration base;
  float minimum_speed;
  float maximum_speed;
  FlightProfile nominal_flight_profile;
  FlightProfile* alternate_flight_profiles;
  size_t alternate_flight_profiles_len;
  LoiterType* available_loiter_types;
  size_t available_loiter_types_len;
  TurnType* available_turn_types;
  size_t available_turn_types_len;
  float minimum_altitude;
  AltitudeType min_altitude_type;
  float maximum_altitude;
  AltitudeType max_altitude_type;
} AirVehicleConfiguration;

typedef struct {
  double latitude;
  double longitude;
  float altitude;
  AltitudeType altitude_type;
} Location3D;

typedef struct {
  int64_t payload_id;
  KeyValuePair* parameters;
  size_t parameters_len;
} PayloadState;

typedef struct {
  int64_t id;
  float u;
  float v;
  float w;
  float udot;
  float vdot;
  float wdot;
  float heading;
  float pitch;
  float roll;
  float p;
  float q;
  float r;
  float course;
  float groundspeed;
  Location3D location;
  float energy_available;
  float actual_energy_rate;
  PayloadState* payload_state_list;
  size_t payload_state_list_len;
  int64_t current_waypoint;
  int64_t current_command;
  NavigationMode mode;
  int64_t* associated_tasks;
  size_t associated_tasks_len;
  int64_t time;
  KeyValuePair* info;
  size_t info_len;
} EntityState;

typedef struct {
  EntityState base;
  float airspeed;
  float vertical_speed;
  float wind_speed;
  float wind_direction;
} AirVehicleState;

typedef struct {
  int64_t* entity_list;
  size_t entity_list_len;
  int64_t* task_list;
  size_t task_list_len;
  const char* task_relationships;
  int64_t operating_region;
  bool redo_all_tasks;
} AutomationRequest;

typedef struct {
  int64_t task_id;
  const char* label;
  int64_t* eligible_entities;
  size_t eligible_entities_len;
  float revisit_rate;
  KeyValuePair* parameters;
  size_t parameters_len;
  uint8_t priority;
  bool required;
} Task;

typedef struct {
  Task base;
  WavelengthBand* desired_wavelength_bands;
  size_t desired_wavelength_bands_len;
  int64_t dwell_time;
  float ground_sample_distance;
} SearchTask;

typedef struct {
  float azimuth_centerline;
  float vertical_centerline;
  float azimuth_extent;
  float vertical_extent;
} Wedge;

typedef struct {
  SearchTask base;
  Location3D* point_list;
  size_t point_list_len;
  Wedge* view_angle_list;
  size_t view_angle_list_len;
  bool use_intertial_view_angles;
} LineSearchTask;

typedef struct {
  int64_t* associated_task_list;
  size_t associated_task_list_len;
} VehicleAction;

typedef struct {
  int64_t command_id;
  int64_t vehicle_id;
  VehicleAction* vehicle_action_list;
  size_t vehicle_action_list_len;
  CommandStatusType status;
} VehicleActionCommand;

typedef struct {
  Location3D base;
  int64_t number;
  int64_t next_waypoint;
  float speed;
  SpeedType speed_type;
  float climb_rate;
  TurnType turn_type;
  VehicleAction* vehicle_action_list;
  size_t vehicle_action_list_len;
  int64_t contingency_waypoint_a;
  int64_t contingency_waypoint_b;
  int64_t* associated_tasks;
  size_t associated_tasks_len;
} Waypoint;

typedef struct {
  VehicleActionCommand base;
  Waypoint* waypoint_list;
  size_t waypoint_list_len;
  int64_t first_waypoint;
} MissionCommand;

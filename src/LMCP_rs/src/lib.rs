// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
 * File:   LMCP.rs
 * Author: acfoltzer
 *
 * Temporary, hand-written translations of the MDMs needed to run Rust examples
 */

extern crate libc;

use libc::{c_char, c_float, c_double, int64_t, size_t, uint8_t};

#[repr(C)]
pub struct AirVehicleConfiguration {
    base: EntityConfiguration,
    pub minimum_speed: c_float,
    pub maximum_speed: c_float,
    pub nominal_flight_profile: FlightProfile,
    pub alternate_flight_profiles: *mut FlightProfile,
    pub alternate_flight_profiles_len: size_t,
    pub available_loiter_types: *mut LoiterType,
    pub available_loiter_types_len: size_t,
    pub available_turn_types: *mut TurnType,
    pub available_turn_types_len: size_t,
    pub minimum_altitude: c_float,
    pub min_altitude_type: AltitudeType,
    pub maximum_altitude: c_float,
    pub max_altitude_type: AltitudeType,
}

impl HasEntityConfiguration for AirVehicleConfiguration {
    fn entity_configuration(self) -> EntityConfiguration { self.base }
}

#[repr(C)]
pub struct AirVehicleState {
    base: EntityState,
    pub airspeed: c_float,
    pub vertical_speed: c_float,
    pub wind_speed: c_float,
    pub wind_direction: c_float,
}

impl HasEntityState for AirVehicleState {
    fn entity_state(self) -> EntityState { self.base }
}

#[repr(C)]
pub enum AltitudeType {
    AGL,
    MSL,
}

#[repr(C)]
pub struct AutomationRequest {
    pub entity_list: *mut int64_t,
    pub entity_list_len: size_t,
    pub task_list: *mut int64_t,
    pub task_list_len: size_t,
    pub task_relationships: *const c_char,
    pub operating_region: int64_t,
    pub redo_all_tasks: bool,
}

#[repr(C)]
pub enum CommandStatusType {
    Pending,
    Approved,
    InProcess,
    Executed,
}

pub trait HasEntityConfiguration {
    fn entity_configuration(self) -> EntityConfiguration;
}

#[repr(C)]
pub struct EntityConfiguration {
    pub id: int64_t,
    pub affiliation: *const c_char,
    pub entity_type: *const c_char,
    pub label: *const c_char,
    pub nominal_speed: c_float,
    pub nominal_altitude: c_float,
    pub nominal_altitude_type: AltitudeType,
    pub payload_configuration_list: *mut PayloadConfiguration,
    pub payload_configuration_list_len: size_t,
    pub info: *mut KeyValuePair,
    pub info_len: size_t,
}

impl HasEntityConfiguration for EntityConfiguration {
    fn entity_configuration(self) -> EntityConfiguration { self }
}

pub trait HasEntityState {
    fn entity_state(self) -> EntityState;
}

#[repr(C)]
pub struct EntityState {
    pub id: int64_t,
    pub u: c_float,
    pub v: c_float,
    pub w: c_float,
    pub udot: c_float,
    pub vdot: c_float,
    pub wdot: c_float,
    pub heading: c_float,
    pub pitch: c_float,
    pub roll: c_float,
    pub p: c_float,
    pub q: c_float,
    pub r: c_float,
    pub course: c_float,
    pub groundspeed: c_float,
    pub location: Location3D,
    pub energy_available: c_float,
    pub actual_energy_rate: c_float,
    pub payload_state_list: *mut PayloadState,
    pub payload_state_list_len: size_t,
    pub current_waypoint: int64_t,
    pub current_command: int64_t,
    pub mode: NavigationMode,
    pub associated_tasks: *mut int64_t,
    pub associated_tasks_len: size_t,
    pub time: int64_t,
    pub info: *mut KeyValuePair,
    pub info_len: size_t,
}

#[repr(C)]
pub struct FlightProfile {
    pub name: *const c_char,
    pub airspeed: c_float,
    pub pitch_angle: c_float,
    pub vertical_speed: c_float,
    pub max_bank_angle: c_float,
    pub energy_rate: c_float,
}

#[repr(C)]
pub struct KeyValuePair {
    pub key: *const c_char,
    pub value: *const c_char,
}

#[repr(C)]
pub struct LineSearchTask {
    base: SearchTask,
    pub point_list: *mut Location3D,
    pub point_list_len: size_t,
    pub view_angle_list: *mut Wedge,
    pub view_angle_list_len: size_t,
    pub use_intertial_view_angles: bool,
}

impl HasSearchTask for LineSearchTask {
    fn search_task(self) -> SearchTask { self.base }
}

pub trait HasLocation3D {
    fn location3d(self) -> Location3D;
}

#[repr(C)]
pub struct Location3D {
    pub latitude: c_double,
    pub longitude: c_double,
    pub altitude: c_float,
    pub altitude_type: AltitudeType,
}

impl HasLocation3D for Location3D {
    fn location3d(self) -> Location3D { self }
}

#[repr(C)]
pub enum LoiterType {
    VehicleDefault = 0,
    Circular = 1,
    Racetrack = 2,
    FigureEight = 3,
    Hover = 4,
}

#[repr(C)]
pub struct MissionCommand {
    base: VehicleActionCommand,
    pub waypoint_list: *mut Waypoint,
    pub waypoint_list_pub: size_t,
    pub first_waypoint: int64_t,
}

impl HasVehicleActionCommand for MissionCommand {
    fn vehicle_action_command(self) -> VehicleActionCommand { self.base}
}

#[repr(C)]
pub enum NavigationMode {
    Waypoint = 0,
    Loiter = 1,
    FlightDirector = 2,
    TargetTrack = 3,
    FollowLeader = 4,
    LostComm = 5,
}

#[repr(C)]
pub struct PayloadConfiguration {
    pub payload_id: int64_t,
    pub payload_kind: *const c_char,
    pub parameters: *mut KeyValuePair,
    pub parameters_len: size_t,
}

#[repr(C)]
pub struct PayloadState {
    pub payload_id: int64_t,
    pub parameters: *mut KeyValuePair,
    pub parameters_len: size_t,
}

pub trait HasSearchTask {
    fn search_task(self) -> SearchTask;
}

#[repr(C)]
pub struct SearchTask {
    base: Task,
    desired_wavelength_bands: *mut WavelengthBand,
    desired_wavelength_bands_len: size_t,
    dwell_time: int64_t,
    ground_sample_distance: c_float,
}

impl<T> HasTask for T where T: HasSearchTask {
    fn task(self) -> Task { self.search_task().base }
}

impl HasSearchTask for SearchTask {
    fn search_task(self) -> SearchTask { self }
}

#[repr(C)]
pub enum SpeedType {
    Airspeed = 0,
    Groundspeed = 1,
}

pub trait HasTask {
    fn task(self) -> Task;
}

#[repr(C)]
pub struct Task {
    pub task_id: int64_t,
    pub label: *const c_char,
    pub eligible_entities: *mut int64_t,
    pub eligible_entities_len: size_t,
    pub revisit_rate: c_float,
    pub parameters: *mut KeyValuePair,
    pub parameters_len: size_t,
    pub priority: uint8_t,
    pub required: bool,
}

impl HasTask for Task {
    fn task(self) -> Task { self }
}

#[repr(C)]
pub enum TurnType {
    TurnShort = 0,
    FlyOver = 1,
}

#[repr(C)]
pub struct VehicleAction {
    pub associated_task_list: *mut int64_t,
    pub associated_task_list_len: size_t,
}

pub trait HasVehicleActionCommand {
    fn vehicle_action_command(self) -> VehicleActionCommand;
}

#[repr(C)]
pub struct VehicleActionCommand {
    pub command_id: int64_t,
    pub vehicle_id: int64_t,
    pub vehicle_action_list: *mut VehicleAction,
    pub vehicle_action_list_len: size_t,
    pub status: CommandStatusType,
}

impl HasVehicleActionCommand for VehicleActionCommand {
    fn vehicle_action_command(self) -> VehicleActionCommand { self }
}

#[repr(C)]
pub enum WavelengthBand {
    AllAny = 0,
    EO = 1,
    LWIR = 2,
    SWIR = 3,
    MWIR = 4,
    Other = 5,
}

#[repr(C)]
pub struct Waypoint {
    base: Location3D,
    pub number: int64_t,
    pub next_waypoint: int64_t,
    pub speed: c_float,
    pub speed_type: SpeedType,
    pub climb_rate: c_float,
    pub turn_type: TurnType,
    pub vehicle_action_list: *mut VehicleAction,
    pub vehicle_action_list_len: size_t,
    pub contingency_waypoint_a: int64_t,
    pub contingency_waypoint_b: int64_t,
    pub associated_tasks: *mut int64_t,
    pub associated_tasks_len: size_t,
}

impl HasLocation3D for Waypoint {
    fn location3d(self) -> Location3D { self.base }
}

#[repr(C)]
pub struct Wedge {
    pub azimuth_centerline: c_float,
    pub vertical_centerline: c_float,
    pub azimuth_extent: c_float,
    pub vertical_extent: c_float,
}

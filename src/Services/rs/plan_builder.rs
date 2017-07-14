//! # PlanBuilderService
//!
//! A component that constructs plans from assignments.
//!
//! 1. For each assigned task option, calculate final task plan.
//! 2. Based on assigned order of task options, calculate final route plans, for
//! each entity, to execute assigned tasks.
//! 3. Construct waypoint plans and send automation response.
//!
//! MESSAGES
//!
//! - ==> TaskAssignmentSummary
//!
//! FOR EVERY TASK
//!
//! - <== TaskImplementationRequest
//! - ==> TaskImplementationResponse
//! - <== RouteRequest
//! - ==> RouteResponse
//! - <== AutomationResponse
//!
//! ## Configuration String
//! `<Service Type="PlanBuilderService" AssignmentStartPointLead_m="50.0" />`
//!
//! ## Options
//! - AssignmentStartPointLead_m
//!
//! ## Subscribed Messages
//! - uxas::messages::task::UniqueAutomationRequest
//! - uxas::messages::task::TaskAssignmentSummary
//! - uxas::messages::task::TaskImplementationResponse
//! - afrl::cmasi::AirVehicleState
//! - afrl::impact::GroundVehicleState
//! - afrl::impact::SurfaceVehicleState
//!
//! ## Sent Messages
//! - afrl::cmasi::ServiceStatus
//! - uxas::messages::task::TaskImplementationRequest
//! - uxas::messages::task::UniqueAutomationResponse

use lmcp_rs::*;
use lmcp_rs::afrl::cmasi::entity_state::*;
use lmcp_rs::afrl::cmasi::key_value_pair::*;
use lmcp_rs::afrl::cmasi::service_status::*;
use lmcp_rs::afrl::cmasi::service_status_type::*;
use lmcp_rs::uxas::messages::task::task_assignment::*;
use lmcp_rs::uxas::messages::task::task_assignment_summary::*;
use lmcp_rs::uxas::messages::task::task_implementation_request::*;
use lmcp_rs::uxas::messages::task::task_implementation_response::*;
use lmcp_rs::uxas::messages::task::unique_automation_request::*;

use std::borrow::BorrowMut;
use std::collections::*;
use std::ptr;
use std::slice;

pub enum CppPlanBuilder {}

#[derive(Debug)]
#[repr(C)]
pub struct PlanBuilder {
    /// The current automation request
    current_automation_request: UniqueAutomationRequest,

    /// Stored entity states, used to get starting heading, position, and time
    entity_states: HashMap<i64, EntityState>,

    /// After receiving a TaskAssignmentSummary,
    /// TaskImplementationRequests are kept here until ready to send
    task_implementation_requests: HashMap<i64, VecDeque<TaskImplementationRequest>>,

    /// TaskImplementationResponses are stored here until it is time
    /// to construct the UniqueAutomationResponse
    task_implementation_responses: HashMap<i64, VecDeque<TaskImplementationResponse>>,

    /// The last TaskImplementationId (and StartingWaypointId) sent
    /// out. It is incremented by 1 for each new ID. It is reset to
    /// zero each time a new TaskAssignmentSummary is received.
    task_implementation_id: i64,

    /// CommandId used in the last mission command. Incremented by 1
    /// for each new mission command. Assume this ID will be unique
    /// during the lifetime run of the PlanBuilder
    command_id: i64,

    /// Distance in meters to add to the position of the vehicle in
    /// the direction the vehicle is heading to calculate the starting
    /// point for new plans
    assignment_start_point_lead_m: f64,

    instance: *mut CppPlanBuilder,
}

impl Default for PlanBuilder {
    fn default() -> PlanBuilder {
        PlanBuilder {
            current_automation_request: UniqueAutomationRequest::default(),
            entity_states: HashMap::default(),
            task_implementation_requests: HashMap::default(),
            task_implementation_responses: HashMap::default(),
            task_implementation_id: 0,
            command_id: 0,
            assignment_start_point_lead_m: 50.0,
            instance: ptr::null_mut(),
        }
    }
}

const STARTING_WAYPOINT_ID: i64 = 100000000;

#[no_mangle]
pub extern "C" fn plan_builder_new(instance: *mut CppPlanBuilder) -> *mut PlanBuilder {
    let mut pb = PlanBuilder::default();
    pb.instance = instance;
    println!("made one! {:?}", pb);
    // relinquish ownership
    Box::into_raw(Box::new(pb))
}

#[no_mangle]
pub extern "C" fn plan_builder_delete(raw_pb: *mut PlanBuilder) {
    // reclaim ownership so it deallocates
    unsafe { Box::from_raw(raw_pb); }
}

#[no_mangle]
pub extern "C" fn plan_builder_configure(raw_pb: *mut PlanBuilder, lead: f64) {
    unsafe { (*raw_pb).assignment_start_point_lead_m = lead; }
}

#[no_mangle]
pub extern "C" fn plan_builder_process_received_lmcp_message(raw_pb: *mut PlanBuilder, msg_buf: *const u8, msg_len: u32) {
    // reclaim ownership
    let mut pb_box = unsafe { Box::from_raw(raw_pb) };
    let msg_buf_slice = unsafe { slice::from_raw_parts(msg_buf, msg_len as usize) };
    if let Ok(Some(msg)) = lmcp_msg_deser(msg_buf_slice) {
        let pb: &mut PlanBuilder = pb_box.borrow_mut();
        match msg {
            LmcpType::TaskAssignmentSummary(tas) => pb.process_task_assignment_summary(tas),
            _ => ()//println!("Unhandled LMCP message {:?}", msg)
        }
    } else {
        println!("LMCP deserialization error!");
    }
    // relinquish ownership
    Box::into_raw(pb_box);
}

impl PlanBuilder {
    fn process_task_assignment_summary(&mut self, tas: TaskAssignmentSummary) {
        // reset for new set of plans
        self.task_implementation_id = 0;
        self.task_implementation_requests.clear();
        self.task_implementation_responses.clear();

        for ta in tas.task_list {
            self.process_task_assignment(ta, tas.operating_region);
        }

        let mut msgs = Vec::new();
        for (_, tirs) in &mut self.task_implementation_responses {
            if let Some(tir) = tirs.pop_front() {
                println!("sending out a request {:?}", tir);
                msgs.push(LmcpType::TaskImplementationResponse(tir));
            }
        }
        for msg in msgs {
            self.send_shared_lmcp_object_broadcast_message(&msg);
        }
    }

    fn process_task_assignment(&mut self, ta: TaskAssignment, region_id: i64) {
        let mut tir = TaskImplementationRequest::default();

        tir.request_id = self.next_implementation_id();
        tir.starting_waypoint_id = self.starting_waypoint_id();
        tir.vehicle_id = ta.assigned_vehicle;
        tir.task_id = ta.task_id;
        tir.option_id = ta.option_id;
        tir.region_id = region_id;
        tir.time_threshold = ta.time_threshold;

        if !self.task_implementation_requests.contains_key(&ta.assigned_vehicle) {
            self.process_new_entity(&ta, &mut tir);
        }

        let deque = self.task_implementation_requests.entry(ta.assigned_vehicle).or_insert(VecDeque::new());
        deque.push_back(tir);
    }

    fn process_new_entity(&mut self, ta: &TaskAssignment, tir: &mut TaskImplementationRequest) {
        if let Some(planning_state) = self.current_automation_request.planning_states.iter().find(|&ps| ps.entity_id == ta.assigned_vehicle) {
            tir.start_heading = planning_state.planning_heading;
            tir.start_position = planning_state.planning_position.clone();
            tir.start_time = unsafe { get_utc_time_since_epoch_ms() };
        } else if let Some(entity_state) = self.entity_states.get(&ta.assigned_vehicle) {
            tir.start_heading = entity_state.heading;
            tir.start_position = entity_state.location.clone();
            tir.start_time = entity_state.time;
        } else {
            let kv = KeyValuePair {
                key: String::from("No UniqueAutomationResponse\0").into_bytes(),
                value: format!("ERROR::processTaskAssignmentSummary: Entity State for Entity Id[{}] not found!\0", ta.assigned_vehicle).into_bytes(),
            };
            let ss = ServiceStatus {
                status_type: ServiceStatusType::Error,
                info: vec![kv],
                percent_complete: 0.0
            };
            println!("sending ServiceStatus {:?}", ss);
            self.send_shared_lmcp_object_broadcast_message(&LmcpType::ServiceStatus(ss));
            return;
        }
        let (north_m0, east_m0) = convert_latlong_deg_to_northeast_m(tir.start_position.latitude, tir.start_position.longitude);
        let north_m = north_m0 + self.assignment_start_point_lead_m * (tir.start_heading as f64).to_radians().cos();
        let east_m = east_m0 + self.assignment_start_point_lead_m * (tir.start_heading as f64).to_radians().sin();
        let (lat_deg, long_deg) = convert_northeast_m_to_latlong_deg(north_m, east_m);
        tir.start_position.latitude = lat_deg;
        tir.start_position.longitude = long_deg;
    }
}

impl PlanBuilder {
    fn next_implementation_id(&mut self) -> i64 {
        match self.task_implementation_id.checked_add(1) {
            None => panic!("next_implementation_id overflowed!"),
            Some(x) => { self.task_implementation_id = x; x },
        }
    }

    fn starting_waypoint_id(&self) -> i64 {
        match self.task_implementation_id.checked_mul(STARTING_WAYPOINT_ID) {
            None => panic!("starting_waypoint_id overflowed!"),
            Some(x) => x,
        }
    }

    fn next_command_id(&mut self) -> i64 {
        match self.command_id.checked_add(1) {
            None => panic!("next_command_id overflowed!"),
            Some(x) => { self.command_id = x; x },
        }
    }

    fn send_shared_lmcp_object_broadcast_message(&self, obj: &LmcpType) {
        let size = lmcp_msg_size(obj);
        let mut buf: Vec<u8> = vec![0; size];
        lmcp_msg_ser(obj, &mut buf);
        unsafe {
            send_shared_lmcp_object_broadcast_message_raw(self.instance, buf.as_ptr(), size as u32);
        }
    }
}

fn convert_latlong_deg_to_northeast_m(lat_deg: f64, long_deg: f64) -> (f64, f64) {
    let mut north_m = 0.0;
    let mut east_m = 0.0;
    unsafe {
        convert_latlong_deg_to_northeast_m_raw(&lat_deg, &long_deg, &mut north_m, &mut east_m);
    }
    (north_m, east_m)
}

fn convert_northeast_m_to_latlong_deg(north_m: f64, east_m: f64) -> (f64, f64) {
    let mut lat_deg = 0.0;
    let mut long_deg = 0.0;
    unsafe {
        convert_northeast_m_to_latlong_deg_raw(&north_m, &east_m, &mut lat_deg, &mut long_deg);
    }
    (lat_deg, long_deg)
}

extern "C" {
    fn get_utc_time_since_epoch_ms() -> i64;
    fn convert_latlong_deg_to_northeast_m_raw(lat_deg: *const f64, long_deg: *const f64, north_m: *mut f64, east_m: *mut f64);
    fn convert_northeast_m_to_latlong_deg_raw(north_m: *const f64, east_m: *const f64, lat_deg: *mut f64, long_deg: *mut f64);
    fn send_shared_lmcp_object_broadcast_message_raw(instance: *const CppPlanBuilder, buf: *const u8, size: u32);
}

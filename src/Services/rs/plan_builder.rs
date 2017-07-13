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
use lmcp_rs::uxas::messages::task::task_assignment_summary::*;
use lmcp_rs::uxas::messages::task::task_implementation_request::*;
use lmcp_rs::uxas::messages::task::task_implementation_response::*;
use lmcp_rs::uxas::messages::task::unique_automation_request::*;

use std::borrow::BorrowMut;
use std::collections::*;
use std::slice;

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
            assignment_start_point_lead_m: 50.0
        }
    }
}

const STARTING_WAYPOINT_ID: i64 = 100000000;

#[no_mangle]
pub extern "C" fn plan_builder_new() -> *mut PlanBuilder {
    let pb = PlanBuilder::default();
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
            _ => println!("Unhandled LMCP message {:?}", msg)
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
}

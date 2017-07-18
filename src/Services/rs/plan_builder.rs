//! # PlanBuilderService
//!
//! A component that constructs plans from assignments.
//!
//! 1. For each assigned task option, request calculation of final waypoint plan in order
//!
//! 2. Construct resulting waypoint plans and send automation response.
//!
//! MESSAGES
//!
//! - ==> TaskAssignmentSummary
//!
//! FOR EVERY TASK
//!
//! - <== TaskImplementationRequest
//! - ==> TaskImplementationResponse
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
use lmcp_rs::afrl::cmasi::location3d::*;
use lmcp_rs::afrl::cmasi::service_status::*;
use lmcp_rs::afrl::cmasi::service_status_type::*;
use lmcp_rs::uxas::messages::task::planning_state::*;
use lmcp_rs::uxas::messages::task::task_assignment::*;
use lmcp_rs::uxas::messages::task::task_assignment_summary::*;
use lmcp_rs::uxas::messages::task::task_implementation_request::*;
use lmcp_rs::uxas::messages::task::task_implementation_response::*;
use lmcp_rs::uxas::messages::task::unique_automation_request::*;
use lmcp_rs::uxas::messages::task::unique_automation_response::*;

use std::borrow::BorrowMut;
use std::collections::*;
use std::slice;

/// Opaque pointer to the C++ PlanBuilderService object
pub enum PlanBuilderService {}

pub struct PlanBuilder {
    /// Unique automation requests keyed by unique automation request ID
    unique_automation_requests: HashMap<i64, UniqueAutomationRequest>,

    /// In-progress unique automation responses keyed by unique automation request ID
    in_progress_response: HashMap<i64, UniqueAutomationResponse>,

    /// Task assignment summaries keyed by unique automation request ID
    assignment_summaries: HashMap<i64, TaskAssignmentSummary>,

    /// Projected entity states keyed by corresponding unique automation request ID
    projected_entity_states: HashMap<i64, Vec<ProjectedState>>,

    /// Assignments yet to be completed, keyed by corresponding unique automation request ID
    remaining_assignments: HashMap<i64, VecDeque<TaskAssignment>>,

    /// Unique automation request IDs keyed by pending task implementation request ID
    expected_response_ids: HashMap<i64, i64>,

    /// Latest entity states, used to get starting heading, position, and time; keyed by entity ID
    entity_states: HashMap<i64, Box<EntityStateT>>,

    /// The last TaskImplementationId (and StartingWaypointId) sent out. It is incremented by 1 for
    /// each new ID. It is reset to zero each time a new TaskAssignmentSummary is received.
    task_implementation_id: i64,

    /// CommandId used in the last mission command. Incremented by 1 for each new mission
    /// command. Assume this ID will be unique during the lifetime run of the PlanBuilder
    command_id: i64,

    /// Distance in meters to add to the position of the vehicle in the direction the vehicle is
    /// heading to calculate the starting point for new plans
    assignment_start_point_lead_m: f64,
}

#[derive(Clone, Debug)]
pub struct ProjectedState {
    state: PlanningState,
    final_waypoint_id: i64,
    /// ms since epoch
    time: i64,
}

impl Default for PlanBuilder {
    fn default() -> PlanBuilder {
        PlanBuilder {
            unique_automation_requests: HashMap::default(),
            in_progress_response: HashMap::default(),
            assignment_summaries: HashMap::default(),
            projected_entity_states: HashMap::default(),
            remaining_assignments: HashMap::default(),
            expected_response_ids: HashMap::default(),
            entity_states: HashMap::default(),
            task_implementation_id: 1,
            command_id: 1,
            assignment_start_point_lead_m: 50.0,
        }
    }
}

const STARTING_WAYPOINT_ID: i64 = 100000000;

#[no_mangle]
pub extern "C" fn plan_builder_new() -> *mut PlanBuilder {
    let pb = PlanBuilder::default();
    println!("Made a Rust PlanBuilder");
    // relinquish ownership
    Box::into_raw(Box::new(pb))
}

#[no_mangle]
pub extern "C" fn plan_builder_delete(raw_pb: *mut PlanBuilder) {
    // reclaim ownership so it deallocates
    unsafe {
        Box::from_raw(raw_pb);
    }
}

#[no_mangle]
pub extern "C" fn plan_builder_configure(raw_pb: *mut PlanBuilder, lead: f64) {
    unsafe {
        (*raw_pb).assignment_start_point_lead_m = lead;
    }
}

#[no_mangle]
pub extern "C" fn plan_builder_process_received_lmcp_message(
    raw_pbs: *mut PlanBuilderService,
    raw_pb: *mut PlanBuilder,
    msg_buf: *const u8,
    msg_len: u32,
) {
    let msg_buf_slice = unsafe { slice::from_raw_parts(msg_buf, msg_len as usize) };
    if let Ok(Some(msg)) = lmcp_msg_deser(msg_buf_slice) {
        if let (Some(pb), Some(pbs)) = unsafe { (raw_pb.as_mut(), raw_pbs.as_mut()) } {
            match msg {
                LmcpType::TaskAssignmentSummary(tas) => {
                    pb.process_task_assignment_summary(pbs, tas);
                }
                LmcpType::TaskImplementationResponse(tir) => {
                    pb.process_task_implementation_response(pbs, tir)
                }
                LmcpType::AirVehicleState(vs) => {
                    pb.entity_states.insert(vs.id, Box::new(vs));
                }
                LmcpType::GroundVehicleState(vs) => {
                    pb.entity_states.insert(vs.id, Box::new(vs));
                }
                LmcpType::SurfaceVehicleState(vs) => {
                    pb.entity_states.insert(vs.id, Box::new(vs));
                }
                LmcpType::UniqueAutomationRequest(uar) => {
                    let id = uar.request_id;
                    pb.unique_automation_requests.insert(id, uar);
                    // re-initialize state maps, possibly halting completion of an overridden
                    // automation request
                    pb.assignment_summaries.insert(id, TaskAssignmentSummary::default());
                    pb.projected_entity_states.insert(id, Vec::new());
                    pb.remaining_assignments.insert(id, VecDeque::new());
                    pb.in_progress_response.insert(id, UniqueAutomationResponse::default());
                }
                _ => println!("Unhandled LMCP message {:?}", msg),
            }
        }
    } else {
        println!("LMCP deserialization error!");
    }
}

impl PlanBuilder {
    fn process_task_assignment_summary(
        &mut self,
        pbs: &mut PlanBuilderService,
        tas: TaskAssignmentSummary,
    ) -> Result<(), ()> {
        let car_id = tas.corresponding_automation_request_id;

        // validate that this summary corresponds to an existing unique automation request
        if let Some(car) = self.unique_automation_requests.get(&car_id) {

            // ensure that a valid state for each vehicle in the request has been received
            for v in &car.original_request.entity_list {
                if let None = self.entity_states.get(&v) {
                    pbs.send_error(format!(
                        "ERROR::processTaskAssignmentSummary: \
                         Corresponding Unique Automation Request included vehicle ID [{}] which \
                         does not have a corresponding current state!",
                        v
                    ));
                    return Err(());
                }
            }

            // queue up all task assignments to be made
            self.remaining_assignments.insert(
                car_id, VecDeque::from(tas.task_list.clone()),
            );

            // initialize state tracking maps with the current request IDs
            self.assignment_summaries.insert(car_id, tas);
            self.in_progress_response.insert(
                car_id, UniqueAutomationResponse { response_id: car_id, ..Default::default() }
            );

            // project states and save them
            let pes = self.project_entity_states(&car);
            self.projected_entity_states.insert(car_id, pes);

        } else {
            pbs.send_error(format!(
                "ERROR::processTaskAssignmentSummary: \
                 Corresponding Unique Automation Request ID [{}] not found!",
                car_id
            ));
        }

        // send the next request
        self.send_next_task_implementation_request(pbs, car_id)
    }

    fn project_entity_states(&self, car: &UniqueAutomationRequest) -> Vec<ProjectedState> {
        // list all participating vehicles in the assignment
        let participating_vehicles: Vec<i64> = if car.original_request.entity_list.is_empty() {
            self.entity_states.keys().map(|&x| x).collect()
        } else {
            car.original_request.entity_list.clone()
        };

        // project states
        let participating_vehicle_states = participating_vehicles.iter().map(|&x| {
            self.entity_states.get(&x)
        });
        participating_vehicles
            .iter()
            .zip(participating_vehicle_states)
            .map(|(v, oes)| {
                let entity_state = oes.expect("ensured to exist by above validation");
                let ps_state =
                    if let Some(ps) = car.planning_states.iter().find(|&ps| v == &ps.entity_id) {
                        ps.clone()
                    } else {
                        // add in the assignment start point lead distance
                        let pos0 = entity_state.get_location();
                        let hdg = *entity_state.get_heading();
                        let (north_m0, east_m0) =
                            convert_latlong_deg_to_northeast_m(pos0.latitude, pos0.longitude);
                        let north_m = north_m0 +
                            self.assignment_start_point_lead_m * (hdg as f64).to_radians().cos();
                        let east_m = east_m0 +
                            self.assignment_start_point_lead_m * (hdg as f64).to_radians().sin();
                        let (lat_deg, long_deg) =
                            convert_northeast_m_to_latlong_deg(north_m, east_m);
                        let position = Location3D {
                            latitude: lat_deg,
                            longitude: long_deg,
                            ..*pos0
                        };
                        PlanningState {
                            entity_id: *v,
                            planning_heading: hdg,
                            planning_position: position,
                        }
                    };
                ProjectedState {
                    final_waypoint_id: 0,
                    time: *entity_state.get_time(),
                    state: ps_state,
                }
            })
            .collect()
    }

    fn send_next_task_implementation_request(
        &mut self,
        pbs: &mut PlanBuilderService,
        id: i64,
    ) -> Result<(), ()> {
        let mut tir = {
            let uar = self.unique_automation_requests.get(&id).ok_or(())?;
            let ra = self.remaining_assignments.get_mut(&id).ok_or(())?;
            let pes = self.projected_entity_states.get(&id).ok_or(())?;
            let ta = ra.pop_front().ok_or(())?;
            let ps = pes.iter().find(|&ps| {
                ps.state.entity_id == ta.assigned_vehicle
            }).ok_or(())?;
            self.expected_response_ids.insert(self.task_implementation_id, id);
            let neighbors =  pes.iter().filter_map(|ref neighbor| {
                if neighbor.state.entity_id != ps.state.entity_id {
                    Some(neighbor.state)
                } else {
                    None
                }
            }).collect();
            TaskImplementationRequest {
                starting_waypoint_id: ps.final_waypoint_id + 1,
                vehicle_id: ta.assigned_vehicle,
                task_id: ta.task_id,
                option_id: ta.option_id,
                region_id: uar.original_request.operating_region,
                time_threshold: ta.time_threshold,
                start_heading: ps.state.planning_heading,
                start_position: ps.state.planning_position.clone(),
                start_time: ps.time,
                neighbor_locations: neighbors,
                ..Default::default()
            }
        };
        // do this outside of the block above in order to satisfy the borrow checker :(
        tir.request_id = self.next_implementation_id();
        pbs.send_shared_lmcp_object_broadcast_message(
            &LmcpType::TaskImplementationRequest(tir)
        );
        Ok(())
    }
}

impl PlanBuilder {
    fn process_task_implementation_response(
        &mut self,
        pbs: &mut PlanBuilderService,
        tiresp: TaskImplementationResponse,
    ) {

        // if let Some(tireqs) = self.task_implementation_requests.get_mut(&tiresp.vehicle_id) {
        //     if let Some(tireq0) = tireqs.front() {
        //         tireqs.pop_front();
        //         println!("found it!");
        //     } else {
        //         let kv = KeyValuePair {
        //             key: String::from("No UniqueAutomationResponse\0").into_bytes(),
        //             value: format!("ERROR::processTaskImplementationResponse: TaskImplementationId[{}] was not found for Entity Id[{}]!\0", tiresp.response_id, tiresp.vehicle_id).into_bytes(),
        //         };
        //         let ss = ServiceStatus {
        //             status_type: ServiceStatusType::Error,
        //             info: vec![kv],
        //             percent_complete: 0.0
        //         };
        //         println!("sending ServiceStatus {:?}", ss);
        //         self.send_shared_lmcp_object_broadcast_message(&LmcpType::ServiceStatus(ss));
        //         return;
        //     }
        // } else {
        //     return;
        // }
    }
}

impl PlanBuilder {
    fn next_implementation_id(&mut self) -> i64 {
        match self.task_implementation_id.checked_add(1) {
            None => panic!("next_implementation_id overflowed!"),
            Some(x) => {
                self.task_implementation_id = x;
                x
            }
        }
    }

    fn starting_waypoint_id(&self) -> i64 {
        match self.task_implementation_id.checked_mul(
            STARTING_WAYPOINT_ID,
        ) {
            None => panic!("starting_waypoint_id overflowed!"),
            Some(x) => x,
        }
    }

    fn next_command_id(&mut self) -> i64 {
        match self.command_id.checked_add(1) {
            None => panic!("next_command_id overflowed!"),
            Some(x) => {
                self.command_id = x;
                x
            }
        }
    }
}

impl PlanBuilderService {
    fn send_shared_lmcp_object_broadcast_message(&mut self, obj: &LmcpType) {
        let size = lmcp_msg_size(obj);
        let mut buf: Vec<u8> = vec![0; size];
        lmcp_msg_ser(obj, &mut buf);
        unsafe {
            send_shared_lmcp_object_broadcast_message_raw(self, buf.as_ptr(), size as u32);
        }
    }

    fn send_error(&mut self, mut msg: String) {
        msg.push('\0');
        let kv = KeyValuePair {
            key: String::from("No UniqueAutomationResponse\0").into_bytes(),
            value: msg.into_bytes(),
        };
        let ss = ServiceStatus {
            status_type: ServiceStatusType::Error,
            info: vec![kv],
            percent_complete: 0.0,
        };
        println!("sending error ServiceStatus {:?}", ss);
        self.send_shared_lmcp_object_broadcast_message(&LmcpType::ServiceStatus(ss));
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
    fn convert_latlong_deg_to_northeast_m_raw(
        lat_deg: *const f64,
        long_deg: *const f64,
        north_m: *mut f64,
        east_m: *mut f64,
    );
    fn convert_northeast_m_to_latlong_deg_raw(
        north_m: *const f64,
        east_m: *const f64,
        lat_deg: *mut f64,
        long_deg: *mut f64,
    );
    fn send_shared_lmcp_object_broadcast_message_raw(
        instance: *mut PlanBuilderService,
        buf: *const u8,
        size: u32,
    );
}

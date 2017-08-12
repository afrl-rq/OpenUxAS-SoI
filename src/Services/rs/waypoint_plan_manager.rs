mod lmcp {
    pub use lmcp_rs::afrl::cmasi::mission_command::*;
    pub use lmcp_rs::afrl::cmasi::turn_type::*;
    pub use lmcp_rs::afrl::cmasi::waypoint::*;
    pub use lmcp_rs::afrl::cmasi::command_status_type::*;
    pub use lmcp_rs::afrl::cmasi::loiter_action::*;
    pub use lmcp_rs::afrl::cmasi::location3d::*;
    pub use lmcp_rs::afrl::cmasi::gimbal_angle_action::*;
    pub use lmcp_rs::*;
}

pub use lmcp_rs::afrl::cmasi::entity_state::EntityStateT;

use std::slice;

macro_rules! debug_println {
    () =>
        (if cfg!(debug_assertions) {
            println!("[waypoint_plan_manager]\n")
        });
    ($fmt:expr) =>
        (if cfg!(debug_assertions) {
            println!(concat!("[waypoint_plan_manager] ", $fmt))
        });
    ($fmt:expr, $($arg:tt)*) =>
        (if cfg!(debug_assertions) {
            println!(concat!("[waypoint_plan_manager] ", $fmt), $($arg)*)
        });
}

pub enum WaypointPlanManagerService {}

#[repr(C)]
pub struct WaypointPlanManager {
    mission_segments: Vec<lmcp::MissionCommand>,
    id_mission_segment_current: i64,
    vehicle_id: i64,
    number_waypoints_to_serve: i32,
    number_waypoint_overlap: i32,
    loiter_radius_default: f32,
    is_add_loiter_to_end_of_segments: bool,
    is_add_loiter_to_end_of_mission: bool,
    is_loop_back_to_first_task: bool,
    is_set_last_waypoint_speed_to_0: bool,
    is_move_to_next_waypoint: bool,
    turn_type: lmcp::TurnType,
    next_mission_command_to_send: Option<lmcp::MissionCommand>,
    send_new_mission_timer_id: u64,
    time_between_mission_commands_min_ms: i64,
    gimbal_payload_id: i64,
}

impl Default for WaypointPlanManager {
    fn default() -> WaypointPlanManager {
        WaypointPlanManager {
            mission_segments: vec![],
            id_mission_segment_current: 0,
            vehicle_id: -1,
            number_waypoints_to_serve: 100000,
            number_waypoint_overlap: 3,
            loiter_radius_default: 200.0,
            is_add_loiter_to_end_of_segments: false,
            is_add_loiter_to_end_of_mission: false,
            is_loop_back_to_first_task: false,
            is_set_last_waypoint_speed_to_0: false,
            is_move_to_next_waypoint: false,
            turn_type: lmcp::TurnType::TurnShort,
            next_mission_command_to_send: None,
            send_new_mission_timer_id: 0,
            time_between_mission_commands_min_ms: 1000,
            gimbal_payload_id: -1,
        }
    }
}

#[no_mangle]
pub extern "C" fn waypoint_plan_manager_new() -> *mut WaypointPlanManager {
    let pb = WaypointPlanManager::default();
    debug_println!("Made a Rust WaypointPlanManager");
    // relinquish ownership
    Box::into_raw(Box::new(pb))
}

#[no_mangle]
pub extern "C" fn waypoint_plan_manager_delete(raw_pb: *mut WaypointPlanManager) {
    // reclaim ownership so it deallocates
    unsafe { Box::from_raw(raw_pb); }
}

#[no_mangle]
pub extern "C" fn waypoint_plan_manager_configure(
    raw_wp: *mut WaypointPlanManager,
    vehicle_id: i64,
    number_waypoints_to_serve: i32,
    number_waypoint_overlap: i32,
    loiter_radius_default: f32,
    is_add_loiter_to_end_of_segments: bool,
    is_add_loiter_to_end_of_mission: bool,
    is_loop_back_to_first_task: bool,
    is_set_last_waypoint_speed_to_0: bool,
    turn_type: lmcp::TurnType,
    gimbal_payload_id: i64,
) {
    if let Some(manager) = unsafe { raw_wp.as_mut() } {
        manager.vehicle_id = vehicle_id;
        manager.number_waypoints_to_serve = number_waypoints_to_serve;
        manager.number_waypoint_overlap = if number_waypoint_overlap >= 2 {
            number_waypoint_overlap
        } else {
            debug_println!(
                "WARNING::WaypointPlanManagerService::bConfigure:: configuration overridden: m_numberWaypointOverlap set = 2"
            );
            2
        };
        manager.loiter_radius_default = loiter_radius_default;
        manager.is_add_loiter_to_end_of_segments = is_add_loiter_to_end_of_segments;
        manager.is_add_loiter_to_end_of_mission = is_add_loiter_to_end_of_mission;
        manager.is_loop_back_to_first_task = is_loop_back_to_first_task;
        manager.is_set_last_waypoint_speed_to_0 = is_set_last_waypoint_speed_to_0;
        manager.turn_type = turn_type;
        manager.gimbal_payload_id = gimbal_payload_id;
    }
}

#[no_mangle]
pub extern "C" fn waypoint_plan_manager_process_received_lmcp_message(
    raw_wps: *mut WaypointPlanManagerService,
    raw_wp: *mut WaypointPlanManager,
    msg_buf: *const u8,
    msg_len: u32,
) {
    // reclaim ownership
    let wps = unsafe {
        raw_wps.as_mut().expect("C++ WaypointPlanManager  passed as null pointer")
    };
    let manager = unsafe {
        raw_wp.as_mut().expect("Rust waypoint_plan_manager passed as null pointer")
    };
    let msg_buf_slice = unsafe { slice::from_raw_parts(msg_buf, msg_len as usize) };
    if let Ok(Some(msg)) = lmcp::lmcp_msg_deser(msg_buf_slice) {
        match msg {

            lmcp::LmcpType::AirVehicleState(ref avs) => {
                if avs.id() == manager.vehicle_id {
                    if manager.is_move_to_next_waypoint {
                        if let Some(waypoint_id_next) = manager.get_next_waypoint_id(avs.current_waypoint()) {
                            manager.next_mission_command_to_send = manager.get_current_segment(waypoint_id_next);
                        }
                        manager.is_move_to_next_waypoint = false;
                    } else {
                        manager.next_mission_command_to_send = manager.get_current_segment(avs.current_waypoint);
                    }
                }
            },

            lmcp::LmcpType::AutomationResponse(ref rsp) => {
                if let Some(mission) = rsp.mission_command_list.iter()
                    .find(|m| m.vehicle_id() == manager.vehicle_id)
                {
                    if manager.initialize_plan(mission.as_ref(), wps) {
                        let waypoint_id_current = mission.waypoint_list()[0].number();
                        manager.next_mission_command_to_send = manager.get_current_segment(waypoint_id_current);
                    }
                }
            },

            // If we get a MissionCommand, we want to initialize
            // our internal state from that message
            lmcp::LmcpType::MissionCommand(ref cmd) if cmd.vehicle_id == manager.vehicle_id => {
                if manager.initialize_plan(cmd, wps) {
                    let waypoint_id_current = cmd.waypoint_list[0].number();
                    if let Some(segment) = manager.get_current_segment(waypoint_id_current) {
                        manager.id_mission_segment_current = segment.command_id;
                    }
                }
            },

            lmcp::LmcpType::MissionCommand(_) => (),

            _ => debug_println!("Unhandled LMCP message {:?}", msg),
        }

    } else {
        debug_println!("LMCP deserialization error!");
    }
}

#[no_mangle]
pub extern "C" fn waypoint_plan_manager_on_send_new_mission_timer(
    raw_wp: *mut WaypointPlanManager,
    raw_wps: *mut WaypointPlanManagerService,
) {
    let wps = unsafe {
        raw_wps.as_mut().expect("C++ WaypointPlanManager  passed as null pointer")
    };
    let manager = unsafe {
        raw_wp.as_mut().expect("Rust waypoint_plan_manager passed as null pointer")
    };

    manager.on_send_new_mission_timer(wps);
}

impl WaypointPlanManager {
    fn initialize_plan(
        &mut self,
        cmd: &lmcp::MissionCommandT,
        raw_wpm: &mut WaypointPlanManagerService
    ) -> bool {
        if self.vehicle_id <= 0 {
            debug_println!("vehicle ID not > 0");
            return false;
        }

        self.mission_segments.clear();
        if !cmd.waypoint_list().is_empty() {

            // setup a template for the mission commands
            let mission_command_temp = lmcp::MissionCommand {
                vehicle_id: self.vehicle_id,
                status: lmcp::CommandStatusType::Approved,
                first_waypoint: -1, // uninitialized
                ..lmcp::MissionCommand::default()
            };

            let mut mission_segment_01 = lmcp::MissionCommand {
                command_id: raw_wpm.get_unique_entity_send_message_id(),
                ..mission_command_temp.clone()
            };
            let mut mission_segment_02 = lmcp::MissionCommand {
                command_id: raw_wpm.get_unique_entity_send_message_id(),
                ..mission_command_temp.clone()
            };

            for wp in cmd.waypoint_list().iter() {
                let mut wp = wp.clone();
                *wp.turn_type_mut() = self.turn_type;

                if mission_segment_01.waypoint_list.len() < self.number_waypoints_to_serve as usize {
                    mission_segment_01.waypoint_list.push(wp.clone());

                    // check for overlap
                    let overlap = self.number_waypoints_to_serve as usize -
                        mission_segment_01.waypoint_list.len();
                    if overlap < self.number_waypoint_overlap as usize {
                        mission_segment_02.waypoint_list.push(wp.clone());
                    }

                    // commanded first waypoint is the second one in
                    // the plan, unless there is only one waypoint
                    if mission_segment_01.waypoint_list.len() <= 2 {
                        mission_segment_01.first_waypoint = wp.number();
                    }
                    if mission_segment_02.waypoint_list.len() <= 2 {
                        mission_segment_02.first_waypoint = wp.number();
                    }

                } else {
                    mission_segment_02.waypoint_list.push(wp.clone());
                    if mission_segment_01.first_waypoint < 0 {
                        debug_println!("first waypoint of segment was not set");
                        return false;
                    }

                    if self.is_add_loiter_to_end_of_segments {
                        let wp_current = &mut mission_segment_01.waypoint_list.last_mut().unwrap();

                        let loiter_action = lmcp::LoiterAction {
                            radius: self.loiter_radius_default,
                            duration: -1,
                            airspeed: wp_current.speed(),
                            location: Box::new(lmcp::Location3D {
                                latitude: wp_current.latitude(),
                                longitude: wp_current.longitude(),
                                altitude: wp_current.altitude(),
                                altitude_type: wp_current.altitude_type(),
                            }),
                            ..lmcp::LoiterAction::default()
                        };

                        wp_current.vehicle_action_list_mut().push(Box::new(loiter_action));
                    }

                    self.mission_segments.push(mission_segment_01);
                    mission_segment_01 = mission_segment_02;
                    mission_segment_02 = lmcp::MissionCommand {
                        command_id: raw_wpm.get_unique_entity_send_message_id(),
                        ..mission_command_temp.clone()
                    };
                }
            }

            if mission_segment_01.first_waypoint >= 0 {
                // final segment
                self.mission_segments.push(mission_segment_01);
            }

            if !self.mission_segments.is_empty() {

                // we might not need the first task number, but just
                // in case, we should get it now so we aren't trying
                // to read it when we've mutably borrowed some other
                // part of the list
                let first_task_num = self.mission_segments.first().unwrap().
                    waypoint_list.first().unwrap().number();
                let wp_last = &mut self.mission_segments.last_mut().unwrap()
                    .waypoint_list.last_mut().unwrap();

                if self.is_add_loiter_to_end_of_mission {

                    let loiter_action = lmcp::LoiterAction {
                        radius: self.loiter_radius_default,
                        duration: -1,
                        airspeed: if self.is_set_last_waypoint_speed_to_0 { 0.0 } else { wp_last.speed() },
                        location: Box::new(lmcp::Location3D {
                            latitude: wp_last.latitude(),
                            longitude: wp_last.longitude(),
                            altitude: wp_last.altitude(),
                            altitude_type: wp_last.altitude_type(),
                        }),
                        ..lmcp::LoiterAction::default()
                    };

                    wp_last.vehicle_action_list_mut().push(Box::new(loiter_action));

                }

                if self.gimbal_payload_id > 0 {
                    // point the camera out in front of the vehicle
                    let gimbal_angle_action = lmcp::GimbalAngleAction {
                        payload_id: self.gimbal_payload_id,
                        elevation: -60.0,
                        ..lmcp::GimbalAngleAction::default()
                    };

                    wp_last.vehicle_action_list_mut().push(Box::new(gimbal_angle_action));
                }

                if self.is_set_last_waypoint_speed_to_0 {
                    *wp_last.speed_mut() = 0.0;
                }

                if self.is_loop_back_to_first_task {
                    *wp_last.next_waypoint_mut() = first_task_num;
                }

            }
        }
        true
    }

    fn get_current_segment(&mut self, current: i64) -> Option<lmcp::MissionCommand> {
        let mut segment_tmp = None;
        for segment in self.mission_segments.iter() {
            for (wp_id, waypoint) in segment.waypoint_list.iter().enumerate() {
                // if possible, don't choose a segment where the
                // desired waypoint is first, unless it is the first
                // segment
                if waypoint.number() == current && (wp_id != 0 || segment_tmp.is_none()) {
                    segment_tmp = Some(segment);
                }
            }
        }

        match segment_tmp {
            Some(segment) if segment.command_id != self.id_mission_segment_current => {
                debug_println!(
                    "New segment: id_mission_segment_new[{:?}] \
                     id_mission_segment_old[{:?}] \
                     waypoint_id_current[{:?}] \
                     first segment waypoint[{:?}] \
                     last[{:?}]",
                    segment.command_id,
                    self.id_mission_segment_current,
                    current,
                    segment.waypoint_list[0].number(),
                    segment.waypoint_list.last().unwrap().number(),
                );
                self.id_mission_segment_current = segment.command_id;
                let mut segment_local = segment.clone();

                if current != segment_local.waypoint_list[0].number() {
                    segment_local.first_waypoint = current;
                }
                Some(segment.clone())
            },
            _ => None,
        }
    }

    fn get_next_waypoint_id(&self, current: i64) -> Option<i64> {
        self.mission_segments.iter().filter_map(
            |segment| segment.waypoint_list.iter().skip_while(
                |wp| wp.number() != current).nth(1)
        ).nth(0).map(|wp| wp.number())
        // for segment in self.mission_segments.iter() {
        //     let mut is_found_current = false;
        //     for waypoint in segment.waypoint_list.iter() {
        //         if waypoint.number() == current {
        //             is_found_current = true;
        //         } else if is_found_current {
        //             return Some(waypoint.number());
        //         }
        //     }
        // }
        // None
    }

    fn on_send_new_mission_timer(
        &mut self,
        raw_wpm: &mut WaypointPlanManagerService,
    ) {
        if let Some(ref payload) = self.next_mission_command_to_send {
            raw_wpm.send_shared_lmcp_object_broadcast_message(
                &lmcp::LmcpType::MissionCommand(payload.clone())
            );
        }
        self.next_mission_command_to_send = None;
    }

}

impl WaypointPlanManagerService {
    pub fn get_unique_entity_send_message_id(&mut self) -> i64 {
        unsafe {
            get_unique_entity_send_message_id_raw(self)
        }
    }

    pub fn send_shared_lmcp_object_broadcast_message(
        &mut self,
        obj: &lmcp::LmcpType,
    ) {
        debug_println!("sending LMCP message {:#?}", obj);
        let size = lmcp::lmcp_msg_size(obj);
        let mut buf: Vec<u8> = vec![0; size];
        let res = lmcp::lmcp_msg_ser(obj, &mut buf);
        if res.is_ok() {
            unsafe {
                send_shared_lmcp_object_broadcast_message_raw(
                    self,
                    buf.as_ptr(),
                    size as u32,
                );
            }
        } else {
            panic!("LMCP serialization failed!");
        }
    }
}

extern {
    fn get_unique_entity_send_message_id_raw(
        instance: *mut WaypointPlanManagerService
    ) -> i64;

    fn send_shared_lmcp_object_broadcast_message_raw(
        instance: *mut WaypointPlanManagerService,
        buf: *const u8,
        size: u32,
    );
}

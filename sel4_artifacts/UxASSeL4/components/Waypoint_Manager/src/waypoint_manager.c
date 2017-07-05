#include <tb_Waypoint_Manager.h>
void in_mission(const MissionSoftware__mission_command_impl * mission) {
	printf("waypoint_manager.c:in_mission -- Received mission with address: %x\n",mission);
}

void in_waypoint(const MissionSoftware__mission_command_impl * waypoint) {
	printf("waypoint_manager.c:in_waypoint -- Received waypoint with address: %x\n",waypoint);
}

void in_send_success(const bool * success) {
	printf("waypoint_manager.c:in_send_success -- Received success value of: %i\n",*success);
}

/* void alarm(const int64_t * periodic_100_m) {} */

void component_entry(const int64_t *n) { }

void component_init(const int64_t *n) { }

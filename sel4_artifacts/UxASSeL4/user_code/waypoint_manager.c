void in_mission(const MissionSoftware__mission_impl * mission) {
	printf("waypoint_manager.c:in_mission -- Received mission with address: %x\n",mission);
}

void in_waypoint(const MissionSoftware__waypoint_impl * waypoint) {
	printf("waypoint_manager.c:in_waypoint -- Received waypoint with address: %x\n",waypoint);
}

/* void alarm(const int64_t * periodic_100_m) {} */

void component_entry(const int64_t *n) { }

void component_init(const int64_t *n) { }
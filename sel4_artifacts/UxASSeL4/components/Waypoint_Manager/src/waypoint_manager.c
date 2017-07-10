#include <stdio.h>
#include <tb_Waypoint_Manager.h>

void component_entry(const int64_t * periodic_dispatcher) {

}

void component_init(const int64_t *arg) {

}

void mission_write(const uint32_t * tb_mission_write) {
    printf("WM saw mission right from the VM\n");
    uint32_t numBytes = 42;
    mission_read(&numBytes);
}

void waypoint_write(const uint32_t * tb_waypoint_write) {
	printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}


void in_send_success(const bool * tb_in_send_success){

}

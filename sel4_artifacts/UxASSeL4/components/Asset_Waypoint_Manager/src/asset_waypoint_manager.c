#include <stdbool.h>
#include <stdio.h>
#include <tb_Asset_Waypoint_Manager.h>

void component_entry(const int64_t * periodic_dispatcher){

}

void component_init(const int64_t *arg){

}

void mission_read_vm(const bool * tb_waypoint_read_vm) {
	printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}


void mission_read_wm(const bool * tb_waypoint_read_wm) {
	printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}


void in_uart_packet(const SMACCM_DATA__UART_Packet_i * tb_in_uart_packet){


}

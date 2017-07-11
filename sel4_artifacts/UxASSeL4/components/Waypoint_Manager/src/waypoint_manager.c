#include <stdio.h>
#include <tb_Waypoint_Manager.h>
#include <camkes.h>

//extern MissionSoftware__mission_command_impl mission;

void component_entry(const int64_t * periodic_dispatcher) {

}

void component_init(const int64_t *arg) {

}

void mission_write(const uint32_t * tb_mission_write) {
    uint32_t i;
    SMACCM_DATA__UART_Packet_i packet;
    printf("WM saw mission write of %d bytes from the VM\n", *tb_mission_write);

    packet.buf_len = 255; 
    for(i = 0; i < *tb_mission_write; i++){
        packet.buf[i % 255] = (*mission)[i];
        if(i % 255 == 254){
            out_uart_packet(&packet);
        }
    }
    packet.buf_len = i % 255;
    out_uart_packet(&packet);

    mission_read(tb_mission_write);
}

void waypoint_write(const uint32_t * tb_waypoint_write) {
	//printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}


void in_send_success(const bool * tb_in_send_success){
    //printf("WM Received ack from UART\n");

}

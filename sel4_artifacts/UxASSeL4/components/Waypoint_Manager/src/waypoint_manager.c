#include <stdio.h>
#include <tb_Waypoint_Manager.h>
#include <camkes.h>

//extern MissionSoftware__mission_command_impl mission;

bool missionSendState = false;
bool uartPacketSent = false;
uint32_t sendBytes;
void component_entry(const int64_t * periodic_dispatcher) {
    static uint32_t i = 0;
    SMACCM_DATA__UART_Packet_i packet;

    if(missionSendState && uartPacketSent){
        uartPacketSent = false;
        packet.buf_len = 255; 
        for(; i < sendBytes; i++){
            packet.buf[i % 255] = (*mission)[i];
            if(i % 255 == 254){
                out_uart_packet(&packet);
                i++;
                return;
            }
        }
        packet.buf_len = i % 255;
        i = 0;
        missionSendState = false;
        out_uart_packet(&packet);
        mission_read(&sendBytes);
    }
}

void component_init(const int64_t *arg) {

}

void mission_write(const uint32_t * tb_mission_write) {
    //printf("WM saw mission write of %d bytes from the VM\n", *tb_mission_write);
    missionSendState = true;
    uartPacketSent = true;
    sendBytes = *tb_mission_write;
}

void waypoint_write(const uint32_t * tb_waypoint_write) {
	//printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}


void in_send_success(const bool * tb_in_send_success){
    //printf("WM Received ack from UART\n");
    uartPacketSent = true;
}

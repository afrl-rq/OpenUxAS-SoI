#include <stdio.h>
#include <tb_Asset_Waypoint_Manager.h>
#include <camkes.h>
#include <mcutils.h>

//static uint32_t LMCP_CTRL_STR = 0x4c4d4350;
static uint32_t LMCP_CTRL_STR_NTWK_ORD = 0x50434d4c;
static mc_t mc;
static bool vm_got_mission_command = true;

void component_entry(const int64_t * periodic_dispatcher){

}

void component_init(const int64_t *arg){

}

void mission_read_vm(const bool * _UNUSED) {
        //printf("Asset Manager confirmed read\n");
        vm_got_mission_command = true;
}


void mission_read_wm(const const bool * _UNUSED) {
	printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}

bool check_ctrl_str(const SMACCM_DATA__UART_Packet_i * tb_in_uart_packet, uint32_t * i){
    static uint8_t ctrl_str_index = 0;
    for(; *i < tb_in_uart_packet->buf_len && ctrl_str_index != sizeof(uint32_t); (*i)++){
        if(tb_in_uart_packet->buf[*i] == ((uint8_t *) &LMCP_CTRL_STR_NTWK_ORD)[ctrl_str_index]){
            ctrl_str_index++;
        }else{
            ctrl_str_index = 0;
        }
    }
    if(ctrl_str_index == sizeof(uint32_t)){
        ctrl_str_index = 0;
        return true;
    }
    return false;

}

bool get_message_size(const SMACCM_DATA__UART_Packet_i * tb_in_uart_packet, size_t * message_size, uint32_t * i){
    static int message_size_index = 0;
    for(; *i < tb_in_uart_packet->buf_len && message_size_index != sizeof(uint32_t); (*i)++, message_size_index++){
        ((uint8_t *) message_size)[message_size_index] = tb_in_uart_packet->buf[*i];
    }
    if(message_size_index == sizeof(uint32_t)){
        BSWAP(*message_size);
        *message_size += sizeof(uint32_t); //also add the checksum size
        message_size_index = 0;
        return true;
    }
    return false;
}

void in_uart_packet(const SMACCM_DATA__UART_Packet_i * tb_in_uart_packet){

    static size_t message_index;
    static size_t message_size;
    static bool gotCtrlStr = false;
    static bool gotSize = false;
    uint32_t i = 0;
    uint8_t sizeIndex;

    while(i < tb_in_uart_packet->buf_len){
        if(!gotCtrlStr){
            gotCtrlStr = check_ctrl_str(tb_in_uart_packet, &i);
            if(gotCtrlStr){
                memcpy(waypoint, &LMCP_CTRL_STR_NTWK_ORD, sizeof(uint32_t));
            }
        }

        if(gotCtrlStr && !gotSize){
            gotSize = get_message_size(tb_in_uart_packet, &message_size, &i);
            if(gotSize){
                message_index = 0;
                memcpy(((uint8_t *)waypoint + 4), &message_size, sizeof(uint32_t));
            //    printf("got message of size: %d\n", message_size);
            }
        }

        if(gotSize){
            for(; i < tb_in_uart_packet->buf_len && message_index < message_size; i++, message_index++){
                ((uint8_t *)&mc + 8)[message_index] = tb_in_uart_packet->buf[i];
            }
            if(message_index == message_size){
                if(vm_got_mission_command){
                    *(mc_t *)waypoint = mc;
                    message_size += 8;
                    waypoint_write(&message_size);
                    vm_got_mission_command = false;
                }
                gotCtrlStr = gotSize = false;
                message_index = 0;
            }

        }
    }
}

#include <stdio.h>
#include <string.h>
#include <tb_Asset_Waypoint_Manager.h>
#include <camkes.h>

//static uint32_t LMCP_CTRL_STR = 0x4c4d4350;
static uint32_t LMCP_CTRL_STR_NTWK_ORD = 0x50434d4c;
static uint8_t * msgbuf;
static bool vm_got_mission_command = true;
static bool wm_got_mission_command = true;

#define DEBUG(fmt,args...) \
  printf("%s,%s,%i:"fmt,__FUNCTION__,"asset_waypoint_manager.c",__LINE__,##args)


#define BSWAP(E) (sizeof(E) == 8 ? E = __builtin_bswap64(E) :\
                  (sizeof(E) == 4 ? E = __builtin_bswap32(E) :\
                   (sizeof(E) == 2 ? E = __builtin_bswap16(E) :\
                    assert(false))))

void component_entry(const int64_t * periodic_dispatcher){

}

void component_init(const int64_t *arg){
  msgbuf = calloc(1,sizeof(*waypoint));
}

void mission_read_vm(const bool * _UNUSED) {
        vm_got_mission_command = true;
}


void mission_read_wm(const const bool * _UNUSED) {
        wm_got_mission_command = true;
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

#define UART_PACKET_SZ 255


/*void in_uart_packet(const SMACCM_DATA__UART_Packet_i * tb_in_uart_packet){
  static bool in_msg = false;
  static uint32_t recv = 0;
  static uint8_t remain[UART_PACKET_SZ];
  static uint32_t remainsz = 0;

  if(in_msg == true) {
    uint32_t msgsz = *((uint32_t*)(msgbuf + 4));
    msgsz = BSWAP(msgsz);
    uint32_t bufsz = tb_in_uart_packet->buf_len;
    memcpy(msgbuf+recv,tb_in_uart_packet->buf,bufsz<(msgsz-recv)?bufsz:msgsz-recv);
    if(bufsz>(msgsz-recv)) {
      memcpy(remain,tb_in_uart_packet->buf+(msgsz-recv)+1,bufsz-(msgsz-recv));
    }
    if(bufsz>(msgsz-recv)) {
    
    }
  }

}*/

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
                memcpy(msgbuf, &LMCP_CTRL_STR_NTWK_ORD, sizeof(uint32_t));
            }
        }

        if(gotCtrlStr && !gotSize){
            gotSize = get_message_size(tb_in_uart_packet, &message_size, &i);
            if(gotSize){
                if(message_size > sizeof(*waypoint) - 8){
                    printf("Received LMCP message of size %u is too big to decode\n", &message_size);
                    gotCtrlStr = gotSize = false;
                    continue;
                }
                message_index = 0;
                BSWAP(message_size);
                memcpy(msgbuf + 4, (uint8_t*) &message_size, sizeof(uint32_t));
                BSWAP(message_size);
                //printf("asset got message of size: %d\n", message_size);
            }
        }

        if(gotSize){
            for(; i < tb_in_uart_packet->buf_len && message_index < message_size; i++, message_index++){
              (msgbuf + 8)[message_index] = tb_in_uart_packet->buf[i];
            }
            //printf("message_index %u, message_size %u\n",message_index,message_size);
            if(message_index == message_size){
                if(wm_got_mission_command){
                  memcpy(*waypoint,msgbuf,sizeof(*waypoint));
                  message_size += 8;
                  waypoint_write(&message_size);
                  vm_got_mission_command = false;
                  wm_got_mission_command = false;
                }
                gotCtrlStr = gotSize = false;
                message_index = 0;
            }

        }
    }
    } 

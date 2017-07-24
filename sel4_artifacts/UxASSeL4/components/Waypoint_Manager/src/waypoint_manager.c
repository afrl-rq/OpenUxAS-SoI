#include <stdio.h>
#include <strings.h>
#include <tb_Waypoint_Manager.h>
#include <camkes.h>
#include <mcutils.h>
#include <AirVehicleState.h>
#include <lmcp.h>

#define MAX_AP_WAYPOINTS 8
#define DEBUG(fmt,args...)  ;//  printf("%s,%s,%i:"fmt,__FUNCTION__,"waypoint_manager.c",__LINE__,##args)

#define UART_PACKET_SZ 255


static bool valid_mc = false;
static mc_t mc = {};
static mc_t swin = {};

static bool valid_nw = false;
static mc_t nw = {};

static void send_swin();

bool missionSendState = false;
bool uartPacketSent = false;
//uint8_t bigBuf[6975];
uint8_t * bigBuf;

void component_entry(const int64_t * periodic_dispatcher) {
    send_swin();
}

void component_init(const int64_t *arg) {
  DEBUG("Starting Waypoint_Manager.\n");
  bigBuf = (uint8_t *)malloc(sizeof(uint8_t)*6975);
}

static void send_swin() {
  static size_t i = 0;
  static size_t pkts;
  static size_t remaining;
  SMACCM_DATA__UART_Packet_i packet;
  if(missionSendState && uartPacketSent){
      if(i == 0){
          pkts = MC_SZ(mc.full.waypointssize)/UART_PACKET_SZ;
          remaining = MC_SZ(mc.full.waypointssize) % UART_PACKET_SZ;
          UnFixCopiedMC(&mc);
      }
      while(i < pkts) {
          DEBUG("Packing and sending packet %u/%u.\n",i,pkts);
          packet.buf_len = UART_PACKET_SZ;
          memcpy(packet.buf,((uint8_t*)(mission))+(UART_PACKET_SZ*i),UART_PACKET_SZ);
          uartPacketSent = false;
          assert(out_uart_packet(&packet) == true);
          i++;
          return;
      }
      if( remaining > 0) {
          DEBUG("Packing and sending remianing %u bytes.\n",remaining);    
          packet.buf_len = remaining;
          memcpy(packet.buf,((uint8_t*)(mission))+(UART_PACKET_SZ*pkts),remaining);
          assert(out_uart_packet(&packet) == true);
      }
      uartPacketSent = false;
      missionSendState = false;
      i = 0;
  }
}

void mission_write(const bool * _UNUSED) {
  DEBUG(" Entry.\n");
  if(DeserializeMCFromBuffer((uint8_t *)mission, &mc) != true) {
    DEBUG(" Failed to deserialize buffer.\n");
  } else {
    valid_mc = true;
    DEBUG("Begin mission command output.\n");
    DEBUG("End mission command output.\n");
    assert(MCWaypointSubSequence(&mc,
                                 mc.full.startingwaypoint,
                                 MAX_AP_WAYPOINTS,
                                 &swin) == true);
    PrintMC(stdout,&mc);
    DEBUG("Intial waypoint window created.\n");
    DEBUG("Sending initial window.\n");
    //send_swin();
    DEBUG("Initial window tranmission complete.\n");
    
    //TODO: Send the first sliding window to the AP.
  }
  DEBUG(" Exit.\n");
  
  missionSendState = true;
  uartPacketSent = true;
  return;
}

void waypoint_write(const uint32_t * size) {
  bool _UNUSEDB = false;
  uint32_t type;
  bool location, x;
  unsigned short payloadStateListLen = 0;
  unsigned short payloadParams = 0;
  size_t offset = 0;
  AirVehicleState state;
  uint8_t * waypointNoHeader = (uint8_t *)waypoint + 8*sizeof(uint8_t);
  size_t sizeMinusHeader = *size - 8;
  int i;
  uint8_t ** pWaypointNoHeader = &waypointNoHeader;
  size_t realSize, alwaysFour = 4;
  uint8_t * waypointCopy = waypoint;

  //for(i = 0; i < *size; i++){
  //  if(i % 20 == 0){
  //    printf("\n");
  //  }
  //  printf("%02x",*((uint8_t *)waypoint + i));
  //}
  //printf("\n");

  //memcpy(&type, (uint8_t *)waypoint + 17, sizeof(uint32_t));
  //BSWAP(type);
  //printf("type %d\n", type);
  
  lmcp_unpack_uint32_t(&waypointCopy, &alwaysFour, &realSize); 
  realSize += 12;

  memset(bigBuf, 0, 6975);
  waypointCopy = waypoint;
  printf("about to process!!\n");
  lmcp_process_msg(&waypointCopy, realSize, &bigBuf);
  printf("I'm here chump!!!\n");
  lmcp_pp((lmcp_object *)bigBuf);


  //if(type == 15){
  //  printf("unpacking... size: %d\n", sizeMinusHeader);
  //  lmcp_unpack(&waypointNoHeader, sizeMinusHeader, &lmcp);
  //  printf("unpacked\n");
  //  lmcp_pp(&lmcp);
  //}




  //get the type, we only care about AirVehicleState messages (15)
  //memcpy(&type, (uint8_t *)waypoint + 17, sizeof(uint32_t));
  //BSWAP(type);
  //if(type == 15){
  //  //this is an AirVehicleState message, get thewaypoint number
  //  memcpy(&location, (uint8_t *)waypoint + 83, sizeof(bool));
  //  if(location){
  //    printf("has location\n");
  //    offset += 14;
  //  }
  //  memcpy(&payloadStateListLen, (uint8_t *)waypoint + 92 + offset, sizeof(unsigned short));
  //  while(payloadStateListLen > 0){
  //    memcpy(&x, (uint8_t *) waypoint + 94 + offset, sizeof(bool));
  //    if(x){
  //      offset += 14
  //      //x.pack at 95 + offset
  //      memcpy(&payloadParams, (uint8_t *) waypoint + 113 + offset, sizeof(unsigned short));
  //      while(paloadParams > 0){
  //        memcpy(&x, (uint8_t *) waypoint + 115 + offset, sizeof(bool));
  //        if(x){
  //          //116
  //          offset += 14

  //        }
  //        offset += 1
  //      }

  //    }
  //    offset += 1;

  //  }


  //}
  //printf("type is %u", type);


  waypoint_read(&_UNUSEDB);

  return;
}


void in_send_success(const bool * tb_in_send_success){
  bool _UNUSED;
  uartPacketSent = true;
  //if we are done sending the last packet then we need to
  //alert the VMM
  if(!missionSendState){
      mission_read(&_UNUSED);
  }
}
 

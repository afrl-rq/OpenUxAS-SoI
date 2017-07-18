#include <stdio.h>
#include <strings.h>
#include <tb_Waypoint_Manager.h>
#include <camkes.h>
#include <mcutils.h>

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

void component_entry(const int64_t * periodic_dispatcher) {
    send_swin();
}

void component_init(const int64_t *arg) {
  DEBUG("Starting Waypoint_Manager.\n");
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

void waypoint_write(const uint32_t * _UNUSED) {
  DEBUG(" Entry.");
  if(DeserializeMCFromBuffer((uint8_t *)mission, &nw) != true) {
    DEBUG(" Failed to deserialize buffer.");
  } else {
    valid_nw = true;
    DEBUG("\nBegin next waypoint output.\n");
    //PrintMC(stdout,&nw);
    DEBUG("\nEnd next waypoint output.\n");
    //TODO: Get the waypoint the asset is currently heading towards.
  }
  DEBUG(" Exit.");
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
 

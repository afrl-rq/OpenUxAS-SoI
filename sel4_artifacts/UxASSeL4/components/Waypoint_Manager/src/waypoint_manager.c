#include <stdio.h>
#include <strings.h>
#include <tb_Waypoint_Manager.h>
#include <camkes.h>
#include <mcutils.h>

#define MAX_AP_WAYPOINTS 8
#define DEBUG(fmt,args...)   printf("%s,%s,%i:"fmt,__FUNCTION__,"waypoint_manager.c",__LINE__,##args)

#define UART_PACKET_SZ 255

#define MC_SZ(waypoints) (sizeof(mc_t)-(MAX_WAYPOINTS*sizeof(wp_t))+(waypoints*sizeof(wp_t)))

static bool valid_mc = false;
static mc_t mc = {};
static mc_t swin = {};

static bool valid_nw = false;
static mc_t nw = {};



void component_entry(const int64_t * periodic_dispatcher) {
  //DEBUG("Periodic execution.\n");
}

void component_init(const int64_t *arg) {
  DEBUG("Starting Waypoint_Manager.\n");
}

static void send_swin() {
  SMACCM_DATA__UART_Packet_i packet;
  size_t pkts = MC_SZ(swin.full.waypointssize)/UART_PACKET_SZ;
  for(size_t i = 0; i < pkts; i++) {
    DEBUG("Packing and sending packet %u/%u.\n",i,pkts);
    packet.buf_len = UART_PACKET_SZ;
    memcpy(packet.buf,((char*)(&swin))+(UART_PACKET_SZ*i),UART_PACKET_SZ);
    assert(out_uart_packet(&packet) == true);
  }
  size_t remaining = MC_SZ(swin.full.waypointssize) % UART_PACKET_SZ;
  if( remaining > 0) {
    DEBUG("Packing and sending remianing %u bytes.\n",remaining);    
    packet.buf_len = remaining;
    memcpy(packet.buf,((char*)(&swin))+(UART_PACKET_SZ*pkts),remaining);
    assert(out_uart_packet(&packet) == true);
  }
}

void mission_write(const bool * _UNUSED) {
  DEBUG(" Entry.\n");
  if(DeserializeMCFromBuffer((uint8_t *)mission, &mc) != true) {
    DEBUG(" Failed to deserialize buffer.\n");
  } else {
    mission_read(_UNUSED);
    valid_mc = true;
    DEBUG("Begin mission command output.\n");
    PrintMC(stdout,&mc);
    DEBUG("End mission command output.\n");
    assert(MCWaypointSubSequence(&mc,
                                 mc.full.startingwaypoint,
                                 MAX_AP_WAYPOINTS,
                                 &swin) == true);
    DEBUG("Intial waypoint window created.\n");
    DEBUG("Sending initial window.\n");
    send_swin();
    DEBUG("Initial window tranmission complete.\n");
    
    //TODO: Send the first sliding window to the AP.
  }
  DEBUG(" Exit.\n");
  
  return;
}

void waypoint_write(const bool * _UNUSED) {
  DEBUG(" Entry.");
  if(DeserializeMCFromBuffer((uint8_t *)mission, &nw) != true) {
    DEBUG(" Failed to deserialize buffer.");
  } else {
    mission_read(_UNUSED);
    valid_nw = true;
    DEBUG("\nBegin next waypoint output.\n");
    PrintMC(stdout,&nw);
    DEBUG("\nEnd next waypoint output.\n");
    //TODO: Get the waypoint the asset is currently heading towards.
  }
  DEBUG(" Exit.");
  return;
}


void in_send_success(const bool * tb_in_send_success){

}

#include <stdio.h>
#include <strings.h>
#include <tb_Waypoint_Manager.h>
#include <camkes.h>
#include <lmcp.h>
#include <MissionCommandUtils.h>

// Maximum number of waypoints that will be sent to the autopilot at
// one time.
#define MAX_AP_WAYPOINTS 8


// TODO: These macros should be shared between all components.
#define DEBUG(fmt,args...) \
  printf("%s,%s,%i:"fmt,__FUNCTION__,"waypoint_manager.c",__LINE__,##args)
#define UART_PACKET_SZ 255

static bool missionSendState = false;
static bool sendUartPacket = false;

static lmcp_object * mc = NULL;
static MissionCommandExt swin;

static AirVehicleState * avs = NULL;


uint32_t Checksum(const uint8_t * p, const size_t len)
{
  uint32_t sum = 0;

  /* assumption: p is not NULL. */
  assert(p != NULL);
  
  for (size_t i = 0; i < len; i++) {
    sum += (uint32_t) p[i];
  }
  return sum & 0x00000000FFFFFFFF;
}



static void send_swin() {
  static size_t i = 0;
  static size_t pkts = 0;
  static size_t remaining = 0;
  static uint8_t * msgbuf = NULL;
  static uint8_t * tmsgbuf = NULL;

  SMACCM_DATA__UART_Packet_i packet;
  MissionCommand * tmc = NULL;
  if(missionSendState && sendUartPacket){
    if(i == 0){
      size_t msgsz = lmcp_msgsize((lmcp_object*)&swin)+4;
      DEBUG("Initiate waypoint window transimission of %u bytes.\n",msgsz);
      msgbuf = calloc(1,msgsz);
      DEBUG("Vehicle ID = %lu\n",swin.MissionCommand.super.VehicleID);
      lmcp_make_msg(msgbuf,&swin);
      tmsgbuf = msgbuf;
      lmcp_process_msg(&tmsgbuf,msgsz,&tmc);
      // There is some problem here causing vehicle id's to be different.
      //lmcp_pp(tmc);
      DEBUG("SWIN ADDY: %x\n",&swin);
      uint32_t chksum = Checksum(msgbuf,msgsz-4);
      *((uint32_t *)(msgbuf + msgsz)) = chksum;
      pkts = msgsz/UART_PACKET_SZ;
      remaining = msgsz % UART_PACKET_SZ;
    }
    if(i < pkts) {
      DEBUG("Packing and sending packet %u/%u\n",i,pkts);
      packet.buf_len = UART_PACKET_SZ;
      memcpy(packet.buf,((uint8_t*)(msgbuf))+(UART_PACKET_SZ*i),UART_PACKET_SZ);
      sendUartPacket = false;
      assert(out_uart_packet(&packet) == true);
      i++;
    } else {
      if( remaining > 0 ) {
        DEBUG("Packing and sending remianing %u bytes.\n",remaining);    
        packet.buf_len = remaining;
        memcpy(packet.buf,((uint8_t*)(msgbuf))+(UART_PACKET_SZ*i),remaining);
        assert(out_uart_packet(&packet) == true);
      }
      i = 0;
      pkts = 0;
      remaining = 0;
      free(msgbuf);
      msgbuf = NULL;
      sendUartPacket = false;
      missionSendState = false;
    }
  }
}

void component_entry(const int64_t * periodic_dispatcher) {
  send_swin();
}

void component_init(const int64_t *arg) {
  DEBUG("Starting Waypoint_Manager.\n");
  lmcp_init_MissionCommand(&mc);
  MCEInit(&swin,MAX_AP_WAYPOINTS);
}

void mission_write(const bool * _UNUSED) {

  uint32_t msgsz = 0;
  size_t s = 4;
  uint8_t * tmp_mission = (uint8_t*)mission;
  MissionCommand * local_mc = (lmcp_object *)mc;
  
  DEBUG(" Entry.\n");
  if(mc != NULL) {
    lmcp_free((lmcp_object*)mc);
    mc = NULL;
  }

  assert(lmcp_process_msg((uint8_t **)&tmp_mission,sizeof(*mission),&mc) != -1);
  assert(MCWaypointSubSequence(local_mc,
                               local_mc->FirstWaypoint,
                               MAX_AP_WAYPOINTS,
                               &swin) == true);
  
  missionSendState = true;
  sendUartPacket = true;
  DEBUG(" Exit.\n");
  return;
}

void waypoint_write(const uint32_t * size) {

  uint32_t msgsz = 0;
  size_t s = 4;
  uint8_t * tmp_waypoint = (uint8_t*)waypoint;
  bool _UNUSEDB;
  lmcp_object * lmcp;
  printf("got waypoint of size %d \n", *size);
  
  lmcp_process_msg(&tmp_waypoint, *size, (lmcp_object **)&lmcp); 
  lmcp_pp((lmcp_object *)lmcp);

  lmcp_free(lmcp);

  /*if(mc != NULL) {
    lmcp_free((lmcp_object*)avs);
    mc = NULL;
  }
  
  assert(lmcp_process_msg((uint8_t **)&tmp_waypoint,sizeof(*waypoint),&avs) != -1);


  if(((lmcp_object *)avs)->type == LMCP_MissionCommand_TYPE ) {
    lmcp_pp(avs);
    }*/
    
  // TODO: Process the VehicleActionCommand and get the assets target
  // waypoint. Use that waypoint in a call to
  // GetMCWaypointSubSequence.
  waypoint_read(&_UNUSEDB);
  return;
}


void in_send_success(const bool * tb_in_send_success){
  sendUartPacket = true;
  //if we are done sending the last packet then we need to
  //alert the VMM
  if(!missionSendState){
    DEBUG("Indicate that the mission can change.\n");
    mission_read(tb_in_send_success);
  }
}
 

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

  SMACCM_DATA__UART_Packet_i packet;
  if(missionSendState && sendUartPacket){
    if(i == 0){
      size_t msgsz = lmcp_msgsize((lmcp_object*)&swin)+4;
      DEBUG("Initiate waypoint window transimission of %u bytes.\n",msgsz);
      msgbuf = calloc(1,msgsz);
      lmcp_make_msg(msgbuf,(lmcp_object*)&swin);
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
  MCEInit(&swin,MAX_AP_WAYPOINTS);
}

void mission_write(const bool * _UNUSED) {

  uint8_t * tmp_mission = (uint8_t*)mission;
  MissionCommand * local_mc = NULL;
  
  if(mc != NULL) {
    lmcp_free((lmcp_object*)mc);
    mc = NULL;
  }

  assert(lmcp_process_msg((uint8_t **)&tmp_mission,sizeof(*mission),&mc) != -1);
  local_mc = (MissionCommand *)mc;
  assert(MCWaypointSubSequence(local_mc,
                               local_mc->FirstWaypoint,
                               MAX_AP_WAYPOINTS,
                               &swin) == true);  
  
  missionSendState = true;
  sendUartPacket = true;
  return;
}


void hexDump (char *desc, void *addr, int len) {
    int i;
    unsigned char buff[17];
    unsigned char *pc = (unsigned char*)addr;

    // Output description if given.
    if (desc != NULL)
        printf ("%s:\n", desc);

    if (len == 0) {
        printf("  ZERO LENGTH\n");
        return;
    }
    if (len < 0) {
        printf("  NEGATIVE LENGTH: %i\n",len);
        return;
    }

    // Process every byte in the data.
    for (i = 0; i < len; i++) {
        // Multiple of 16 means new line (with line offset).

        if ((i % 16) == 0) {
            // Just don't print ASCII for the zeroth line.
            if (i != 0)
                printf ("  %s\n", buff);

            // Output the offset.
            printf ("  %04x ", i);
        }

        // Now the hex code for the specific character.
        printf (" %02x", pc[i]);

        // And store a printable ASCII character for later.
        if ((pc[i] < 0x20) || (pc[i] > 0x7e))
            buff[i % 16] = '.';
        else
            buff[i % 16] = pc[i];
        buff[(i % 16) + 1] = '\0';
    }

    // Pad out last line if not exactly 16 characters.
    while ((i % 16) != 0) {
        printf ("   ");
        i++;
    }

    // And print the final ASCII bit.
    printf ("  %s\n", buff);
}

void waypoint_write(const uint32_t * size) {

  uint8_t * tmp_waypoint = (uint8_t*)waypoint;
  bool _UNUSEDB;
  lmcp_object * lmcp;
  int i;
  uint64_t waypointNum;
  uint32_t type;
  uint64_t id;
  Waypoint * wp = NULL;

  //hexDump("waypoint_write recv",(uint8_t*)waypoint,*size);
  
  memcpy(&type, ((uint8_t *)waypoint) + 17, sizeof(uint32_t));
  type = __builtin_bswap32(type);

  if(type == 15){

    memcpy(&id, ((uint8_t *)waypoint) + 23, sizeof(uint64_t));
    id = __builtin_bswap64(id);

    memcpy(&waypointNum, ((uint8_t *)waypoint) + 423, sizeof(uint64_t));
    waypointNum = __builtin_bswap64(waypointNum);

    if(id == 400 && mc != NULL) {
      MissionCommand * local_mc = (MissionCommand *)mc;
      if(waypoint<=0 || FindWP(local_mc,waypointNum,&wp) != true ) {
        DEBUG("Got %li waypoint, resend waypoints:\n",waypointNum);
        missionSendState = true;
        sendUartPacket = true;        
      }
      else if(GetMCWaypointSubSequence(local_mc,
                                  swin.MissionCommand.FirstWaypoint,
                                  waypointNum,
                                  MAX_AP_WAYPOINTS,
                                  &swin)) {
        DEBUG("Update waypoints:\n");
        
        missionSendState = true;
        sendUartPacket = true;
      } else {
      }
    }
  }

  waypoint_read(&_UNUSEDB);
  return;
    


}


void in_send_success(const bool * tb_in_send_success){
  sendUartPacket = true;
  //if we are done sending the last packet then we need to
  //alert the VMM
  if(!missionSendState){
    mission_read(tb_in_send_success);
  }
}
 

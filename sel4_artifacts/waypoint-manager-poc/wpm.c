#include "wpm.h"
#include <string.h>



#define MKSWAP(N) \
  void swap##N(void *v) {\
    uint64_t i;\
    char in[N], out[N];\
    memcpy((void*)in, v, N);\
    for(i = 0;i<N;i++) {\
      out[i] = in[(N-i)-1];\
    }\
    memcpy(v,(void*)out,N);\
  }

MKSWAP(2)

MKSWAP(4)

MKSWAP(8)


bool deserialize_mc(FILE * f, mc_t * mc) {
  fread(mc,sizeof(mc_t),1,f);
  return correct_mc(mc);
}

bool correct_mc(mc_t * mc) {
  uint16_t i;
  
  swap8(&mc->full.commandid);
  swap8(&mc->full.vehicleid);
  swap2(&mc->full.vehicleactionlistsize);
  swap4(&mc->full.commandstatus);
  swap2(&mc->full.waypointssize);
  for(i = 0;i < mc->full.waypointssize; i++) {
    swap8(&(mc->full.waypoints[i].latitude));
    swap8(&(mc->full.waypoints[i].longitude));
    swap4(&(mc->full.waypoints[i].altitude));
    swap4(&(mc->full.waypoints[i].altitude_type));
    swap8(&(mc->full.waypoints[i].id));
    swap8(&(mc->full.waypoints[i].nxid));
    swap4(&(mc->full.waypoints[i].speed));
    swap4(&(mc->full.waypoints[i].speed_type));
    swap4(&(mc->full.waypoints[i].climbrate));
    swap4(&(mc->full.waypoints[i].turntype));
    swap2(&(mc->full.waypoints[i].vehicleactionlistsize));
    swap8(&(mc->full.waypoints[i].contingencywaypointa));
    swap8(&(mc->full.waypoints[i].contingencywaypointb));
    swap2(&(mc->full.waypoints[i].associatedtasksize));
  }
  mc->full.startingwaypoint = *((uint64_t*)(mc->full.waypoints + i));
  swap8(&(mc->full.startingwaypoint));
  mc->full.checksum = *((uint32_t *)(((uint64_t*)(mc->full.waypoints + i)) + 1));
  swap4(&(mc->full.checksum));
  memset(mc->full.waypoints + i, 0, sizeof(wp_t)*(65535-i));
  
  return mc->full.checksum = calculateChecksum((uint8_t *)mc,sizeof(mc_t));
}

void output_mc(FILE * f, mc_t * mc) {
  uint16_t i = 0;
  wp_t wp;

  fprintf(f,"command id: %lu\n",mc->full.commandid);
  fprintf(f,"vehicle id: %lu\n",mc->full.vehicleid);
  fprintf(f,"command status: %u\n",mc->full.commandstatus);
  fprintf(f,"waypoints: %hu\n",mc->full.waypointssize);
  for(i = 0;i < mc->full.waypointssize; i++) {
    wp = mc->full.waypoints[i];
    fprintf(f,"\t waypoint %hu:\n",i+1);    
    fprintf(f,"\t\tlatitude: %lf\n", wp.latitude);
    fprintf(f,"\t\tlongitude: %lf\n", wp.longitude);
    fprintf(f,"\t\taltitude: %f\n", wp.altitude);
    fprintf(f,"\t\taltitude type: %i\n", wp.altitude_type);
    fprintf(f,"\t\tid: %lu\n",wp.id);
    fprintf(f,"\t\tnext id: %lu\n",wp.nxid);
    fprintf(f,"\t\tspeed:%f\n",wp.speed);
    fprintf(f,"\t\tspeed type:%i\n",wp.speed_type);
    fprintf(f,"\t\tclimbrate:%f\n",wp.climbrate);
    fprintf(f,"\t\tturntype:%i\n",wp.turntype);
    fprintf(f,"\t\tvehicle action list size:%hu\n",wp.vehicleactionlistsize);
    fprintf(f,"\t\tcontingency Waypoint A:%lu\n",wp.contingencywaypointa);
    fprintf(f,"\t\tcontingency Waypoint B:%lu\n",wp.contingencywaypointb);
    fprintf(f,"\t\tvehicle action list size:%hu\n",wp.associatedtasksize);
  }
  fprintf(f,"starting waypoint: %lu\n",mc->full.startingwaypoint);
  fprintf(f,"checksum: %u\n",mc->full.checksum);
  return;
}

uint32_t calculateChecksum(const uint8_t * bytes, const uint32_t len)
{
  uint32_t sum = 0;
  for (uint32_t i = 0; i < len - sizeof(uint32_t); i++)
    sum += (uint32_t) bytes[i];
  return sum & 0x00000000FFFFFFFF;
}

bool sub_mc(const mc_t * super, const uint64_t nxid, const uint16_t len, mc_t * sub) {

  uint16_t i;
  wp_t wp;
  uint64_t id = nxid;
  
  memset(sub,0,sizeof(mc_t));
  
  sub->trnc = super->trnc;
  
  for(i=0; i<len; i++) {
    if(find_wp(super,id,&wp) != true) {
      return false;
    }
    if(wp.id == wp.nxid) {
      break;
    }
    sub->full.waypoints[i] = wp;
    id = wp.nxid;
  }

  sub->full.startingwaypoint = nxid;
  sub->full.waypointssize = i;
  sub->full.checksum = calculateChecksum((uint8_t*)sub,sizeof(mc_t));
  return true;

}


bool find_wp(const mc_t * mc, const uint64_t id, wp_t * wp) {

  uint16_t i;

  for(i = 0; i<mc->full.waypointssize; i++) {
    if(mc->full.waypoints[i].id == id) {
      *wp = mc->full.waypoints[i];
      return true;
    }
  }
  
  return false;

}

/******************************************************************************
* Author: Dan DaCosta                                                         *
*                                                                             *
* Purposes: Implements a number of functions useful for mission               *
* command manipulation.                                                       *
******************************************************************************/

#include "wpm.h"
#include <assert.h>
#include <string.h>

/* Swap: Reverse byte ordering for uint8_t arrays.
     
     p - uint8_t array
   
     len - the length of p in uint8_t's
*/
void Swap(uint8_t * p, const size_t len) {
  const size_t MAXLEN = 8;
  char in[MAXLEN], out[MAXLEN];

  /* assumption: p is not NULL. */
  assert(p != NULL);
  
  /* assumption: Swap is never called with len > MAXLEN. */
  assert(len <= MAXLEN);

  memcpy(in, p, len);
  for(size_t i = 0 ; i<len ; i++) {
    out[i] = in[( len - i ) - 1];
  }
  memcpy(p,out,len);
}

/* SWAP: A wrapping macro for use with Swap. */
#define SWAP(V) Swap((uint8_t*)&(V),sizeof(V));

/* Checksum: Calculate the UxAS checksum. */
uint32_t Checksum(const uint8_t * p, const size_t len)
{
  uint32_t sum = 0;

  /* assumption: p is not NULL. */
  assert(p != NULL);
  
  for (size_t i = 0; i < len - sizeof(uint32_t); i++) {
    sum += (uint32_t) p[i];
  }
  return sum & 0x00000000FFFFFFFF;
}

/* FixCopiedMC: Accepts a mission command storing a serialized mission
   command and deserializes it in place.  

   mc_ptr - Mission command to fix.
   
   returns - True if the checksum for the fixed mission command is
   correct, false otherwise.
*/ 
bool FixCopiedMC(mc_t * mc_ptr) {
  uint16_t i;

  /* assumption: p is not NULL. */
  assert(mc_ptr != NULL);

  
  /* Swap the fields in the mission command that are layed out "ahead"
     of the waypoints. */
  SWAP(mc_ptr->full.commandid);
  SWAP(mc_ptr->full.vehicleid);
  SWAP(mc_ptr->full.vehicleactionlistsize);
  SWAP(mc_ptr->full.commandstatus);
  SWAP(mc_ptr->full.waypointssize);
  
  /* Swap all the fields in each waypoint. */
  for(i = 0;i < mc_ptr->full.waypointssize; i++) {
    SWAP(mc_ptr->full.waypoints[i].latitude);
    SWAP(mc_ptr->full.waypoints[i].longitude);
    SWAP(mc_ptr->full.waypoints[i].altitude);
    SWAP(mc_ptr->full.waypoints[i].altitude_type);
    SWAP(mc_ptr->full.waypoints[i].id);
    SWAP(mc_ptr->full.waypoints[i].nxid);
    SWAP(mc_ptr->full.waypoints[i].speed);
    SWAP(mc_ptr->full.waypoints[i].speed_type);
    SWAP(mc_ptr->full.waypoints[i].climbrate);
    SWAP(mc_ptr->full.waypoints[i].turntype);
    SWAP(mc_ptr->full.waypoints[i].vehicleactionlistsize);
    SWAP(mc_ptr->full.waypoints[i].contingencywaypointa);
    SWAP(mc_ptr->full.waypoints[i].contingencywaypointb);
    SWAP(mc_ptr->full.waypoints[i].associatedtasksize);
  }

  /* The serialized waypoints are followed by the starting waypoint. */
  mc_ptr->full.startingwaypoint = *((uint64_t*)(mc_ptr->full.waypoints + i));
  SWAP(mc_ptr->full.startingwaypoint);

  /* The mission command serialization ends with a checksump */
  mc_ptr->full.checksum = *((uint32_t *)(((uint64_t*)(mc_ptr->full.waypoints + i)) + 1));
  SWAP(mc_ptr->full.checksum);

  /* Zeroize the unused waypoints. */
  memset(mc_ptr->full.waypoints + i, 0, sizeof(wp_t) * (65535-i));

  /* Ensure the checksum is correct. */
  return mc_ptr->full.checksum = Checksum((uint8_t *)mc_ptr,sizeof(mc_t));
}


/* DeserializeMCFromFile: Deserialize a mission command read from a
   file. 

     f - The file to read the mission command from.

     mc_ptr - The mission command to be populated from the serialized data.
     
*/
bool DeserializeMCFromFile(FILE * f, mc_t * mc_ptr) {
  /* assumption: mc_ptr is not NULL. */
  assert(mc_ptr != NULL);
  /* assumption: f is not NULL. */
  assert(f != NULL);

  fread(mc_ptr, sizeof(mc_t), 1, f);
  return FixCopiedMC(mc_ptr);
}

/* PrintMC: Output the mission command in human readable form for
   debugging purposes. 

     f - The file to read the mission command from.

     mc_ptr - The mission command to print.

*/
void PrintMC(FILE * f, mc_t * mc_ptr) {
  uint16_t i = 0;

  /* assumption: mc_ptr is not NULL. */
  assert(mc_ptr != NULL);
  /* assumption: f is not NULL. */
  assert(f != NULL);
  
  fprintf(f,"command id: %lu\n",mc_ptr->full.commandid);
  fprintf(f,"vehicle id: %lu\n",mc_ptr->full.vehicleid);
  fprintf(f,"command status: %u\n",mc_ptr->full.commandstatus);
  fprintf(f,"waypoints: %hu\n",mc_ptr->full.waypointssize);
  for(i = 0 ;i < mc_ptr->full.waypointssize ; i++) {
    fprintf(f,"\t waypoint %hu:\n",i+1);    
    fprintf(f,"\t\tlatitude: %lf\n", mc_ptr->full.waypoints[i].latitude);
    fprintf(f,"\t\tlongitude: %lf\n", mc_ptr->full.waypoints[i].longitude);
    fprintf(f,"\t\taltitude: %f\n", mc_ptr->full.waypoints[i].altitude);
    fprintf(f,"\t\taltitude type: %i\n", mc_ptr->full.waypoints[i].altitude_type);
    fprintf(f,"\t\tid: %lu\n",mc_ptr->full.waypoints[i].id);
    fprintf(f,"\t\tnext id: %lu\n",mc_ptr->full.waypoints[i].nxid);
    fprintf(f,"\t\tspeed:%f\n",mc_ptr->full.waypoints[i].speed);
    fprintf(f,"\t\tspeed type:%i\n",mc_ptr->full.waypoints[i].speed_type);
    fprintf(f,"\t\tclimbrate:%f\n",mc_ptr->full.waypoints[i].climbrate);
    fprintf(f,"\t\tturntype:%i\n",mc_ptr->full.waypoints[i].turntype);
    fprintf(f,"\t\tvehicle action list size:%hu\n",
            mc_ptr->full.waypoints[i].vehicleactionlistsize);
    fprintf(f,"\t\tcontingency Waypoint A:%lu\n",
            mc_ptr->full.waypoints[i].contingencywaypointa);
    fprintf(f,"\t\tcontingency Waypoint B:%lu\n",
            mc_ptr->full.waypoints[i].contingencywaypointb);
    fprintf(f,"\t\tvehicle action list size:%hu\n",
            mc_ptr->full.waypoints[i].associatedtasksize);
  }
  fprintf(f,"starting waypoint: %lu\n",mc_ptr->full.startingwaypoint);
  fprintf(f,"checksum: %u\n",mc_ptr->full.checksum);
  return;
}

/* FindWP: Find a waypoint associated with an id. 

     mc_ptr - Pointer to a mission command.

     id - Waypoint identifier to be searched for.

     wp_ptr - Pointer to waypoint where found waypoint will be stored.

     returns - True if the waypoint was found, false otherwise.
*/
bool FindWP(const mc_t * mc_ptr, const uint64_t id, wp_t * wp_ptr) {
  uint16_t i;

  /* assumption: p is not NULL. */
  assert(mc_ptr != NULL);
  /* assumption: f is not NULL. */
  assert(wp_ptr != NULL);
  
  for(i = 0 ; i < mc_ptr->full.waypointssize ; i++) {
    if(mc_ptr->full.waypoints[i].id == id) {
      *wp_ptr = mc_ptr->full.waypoints[i];
      return true;
    }
  }
  
  return false;
}

/* MCPrefix: Create a new mission command from a prefix of the
   waypoints of another mission command. 

     orig_mc_ptr - The mission command whose prefix waypoints will be
     used to build a new mission command.

     id - The waypoint id to start the prefix from.

     len - The length of the prefix.

     new_mc_ptr - The mission command that will stored the prefix
     version of mc_orig_ptr.

*/
bool MCPrefix(const mc_t * orig_mc_ptr,
              const uint64_t id,
              const uint16_t len,
              mc_t * mc_new_ptr) {
  uint16_t i;
  wp_t wp;
  uint64_t idit = id;

  /* assumption: orig_mc_ptr is not NULL. */
  assert(orig_mc_ptr != NULL);
  /* assumption: f is not NULL. */
  assert(mc_new_ptr != NULL);

  /* Ensure that a bad id was not provided. */
  if(FindWP(orig_mc_ptr, id, &wp) != true) {
    return false;
  }

  /* Ensure that a 0 length prefix was not asked for. */
  if(len == 0) {
    return false;
  }
  
  memset(mc_new_ptr,0,sizeof(mc_t));
  
  mc_new_ptr->trnc = orig_mc_ptr->trnc;
  
  for(i=0; i<len; i++) {

    /* assumption: all ids in the waypoint list can be found. */
    assert(FindWP(orig_mc_ptr,idit,&wp) == true);

    if(wp.id == wp.nxid) {
      break;
    }
    mc_new_ptr->full.waypoints[i] = wp;
    idit = wp.nxid;
  }

  mc_new_ptr->full.startingwaypoint = id;
  mc_new_ptr->full.waypointssize = i;
  mc_new_ptr->full.checksum = Checksum((uint8_t*)mc_new_ptr,sizeof(mc_t));
  return true;
}

/* GetMCPrefix: Get a mission command prefix if the waypoint being
   approached by the platform is half way through the previous mission
   command prefix which was assumed to be sent.

     orig_mc_ptr - The mission command whose prefix waypoints will be
     used to build a new mission command.

     last_prefix_start_id - The starting waypoint id of the last
     prefix sent to the auto-pilot.

     ap_wp - The waypoint the auto-pilot is currently heading towards.

     len - The len of the new prefix.

     new_mc_ptr - The storage place of the new prefix mission command.

     returns - True if a new prefix mission command was selected,
     false otherwise.

 */
bool GetMCPrefix(const mc_t * orig_mc_ptr,
                 const uint64_t last_prefix_start_id,
                 const uint64_t ap_id,
                 const uint16_t len,
                 mc_t * new_mc_ptr) {
  uint16_t i;
  wp_t wp;
  uint64_t it_id = last_prefix_start_id;

  /* assumption: orig_mc_ptr is not NULL. */
  assert(orig_mc_ptr != NULL);

  /* assumption: f is not NULL. */
  assert(new_mc_ptr != NULL);

  /* Ensure that a bad last_prefix_start_id was not provided. */
  if(FindWP(orig_mc_ptr, last_prefix_start_id, &wp) != true) {
    return false;
  }

  /* Ensure that a bad ap_id was not provided. */
  if(FindWP(orig_mc_ptr, ap_id, &wp) != true) {
    return false;
  }

  /* Ensure that a 0 length prefix was not asked for. */
  if(len == 0) {
    return false;
  }

  
  /* Check to see if the ap_id is in the first half of the auto-pilot
     length. */
  for(i = 0; i < len/2 ; i++) {
   
    /* assumption: all ids in the waypoint list can be found. */
    assert(FindWP(orig_mc_ptr,it_id,&wp) == true);

    /* If we have found the end or found the nextwp then there is no
       update to be sent to the auto-pilot. */
    if(wp.id == wp.nxid || wp.id == ap_id) {
      return false;
    }

    it_id = wp.nxid;
  }


  for( ; i < len; i++) {
    
    /* assumption: all ids in the waypoint list can be found. */
    assert(FindWP(orig_mc_ptr, it_id, &wp) == true );

    if( wp.id == ap_id ) {
      MCPrefix(orig_mc_ptr, ap_id, len, new_mc_ptr);
      return true;
    }
    
  }

  /* assumption: Control flow should never get here. */
  assert(false);
  return false;
}


#ifdef __WPM_TESTS__

mc_t orig_mc, new_mc;

bool DeserializeAndPrefixTest1() {

  FILE * f = NULL;
  wp_t wp;
  bool pass = true;
  
  memset(&orig_mc, 0, sizeof(mc_t));
  memset(&new_mc, 0, sizeof(mc_t));
  
  f = fopen("missioncommand","r");

  pass = pass & DeserializeMCFromFile(f, &orig_mc);
  pass = pass & MCPrefix(&orig_mc, orig_mc.full.startingwaypoint, 5, &new_mc);
  /*  pass = pass & (memcmp(orig_mc.full.header,
                        new_mc.full.header,
                        MC_HDR_LEN));*/

  /* TODO: Complete checks for equality where relevant. */
  
  return pass;
}

#define TEST(X) fprintf(stdout,\
                        "Test %s: %s\n",\
                        #X,\
                        X() == true ? "Pass" : "Fail")

int main(void) {

  TEST(DeserializeAndPrefixTest1);
  return 0;
}

#endif /* __WPM_TESTS__ */

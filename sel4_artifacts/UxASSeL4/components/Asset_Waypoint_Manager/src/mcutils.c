/******************************************************************************
* Author: Dan DaCosta                                                         *
*                                                                             *
* Purposes: Implements a number of functions useful for mission               *
* command manipulation.                                                       *
*                                                                             *
* Testing build:  $CC -g -D__MCUTILS_TESTS__ wpm.c                                *
******************************************************************************/

#include "mcutils.h"
#include <assert.h>
#include <string.h>

#define BSWAP(E) (sizeof(E) == 8 ? E = __builtin_bswap64(E) :\
                  (sizeof(E) == 4 ? E = __builtin_bswap32(E) :\
                   (sizeof(E) == 2 ? E = __builtin_bswap16(E) :\
                    assert(false))))

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
  BSWAP(mc_ptr->full.commandid);
  BSWAP(mc_ptr->full.vehicleid);
  BSWAP(mc_ptr->full.vehicleactionlistsize);
  BSWAP(mc_ptr->full.commandstatus);
  BSWAP(mc_ptr->full.waypointssize);
  
  /* Swap all the fields in each waypoint. */
  for(i = 0;i < mc_ptr->full.waypointssize; i++) {
    BSWAP(mc_ptr->full.waypoints[i].latitude);
    BSWAP(mc_ptr->full.waypoints[i].longitude);
    BSWAP(mc_ptr->full.waypoints[i].altitude);
    BSWAP(mc_ptr->full.waypoints[i].altitude_type);
    BSWAP(mc_ptr->full.waypoints[i].id);
    BSWAP(mc_ptr->full.waypoints[i].nxid);
    BSWAP(mc_ptr->full.waypoints[i].speed);
    BSWAP(mc_ptr->full.waypoints[i].speed_type);
    BSWAP(mc_ptr->full.waypoints[i].climbrate);
    BSWAP(mc_ptr->full.waypoints[i].turntype);
    BSWAP(mc_ptr->full.waypoints[i].vehicleactionlistsize);
    BSWAP(mc_ptr->full.waypoints[i].contingencywaypointa);
    BSWAP(mc_ptr->full.waypoints[i].contingencywaypointb);
    BSWAP(mc_ptr->full.waypoints[i].associatedtasksize);
  }

  /* The serialized waypoints are followed by the starting waypoint. */
  mc_ptr->full.startingwaypoint = *((uint64_t*)(mc_ptr->full.waypoints + i));
  BSWAP(mc_ptr->full.startingwaypoint);

  /* The mission command serialization ends with a checksump */
  mc_ptr->full.checksum =
    *((uint32_t *)(((uint64_t*)(mc_ptr->full.waypoints + i)) + 1));
  BSWAP(mc_ptr->full.checksum);

  /* Zeroize the unused waypoints. */
  memset(mc_ptr->full.waypoints + i, 0, sizeof(wp_t) * (MAX_WAYPOINTS-i));

  /* Ensure the checksum is correct. */
  return mc_ptr->full.checksum == Checksum((uint8_t *)mc_ptr,sizeof(mc_t));
}


/* DeserializeMCFromFile: Deserialize a mission command reading from a
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


/* DeserializeMCFromBuffer: Deserialize a mission command from a byte
   buffer.

     buf - The buffer storing the mission command.

     mc_ptr - The mission command to be populated from the serialized
     data.
     
*/
bool DeserializeMCFromBuffer(const uint8_t * buf, mc_t * mc_ptr) {
  /* assumption: mc_ptr is not NULL. */
  assert(mc_ptr != NULL);
  /* assumption: f is not NULL. */
  assert(buf != NULL);

  *mc_ptr = *((mc_t*)buf);
  
  return FixCopiedMC(mc_ptr);
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

/* MCWaypointSubSequence: Create a new mission command from a prefix of the
   waypoints of another mission command. 

     orig_mc_ptr - The mission command whose prefix waypoints will be
     used to build a new mission command.

     id - The waypoint id to start the prefix from.

     len - The length of the prefix.

     new_mc_ptr - The mission command that will stored the prefix
     version of mc_orig_ptr.

*/
bool MCWaypointSubSequence(const mc_t * orig_mc_ptr,
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

  mc_new_ptr->full.waypoints[i - 1].nxid = mc_new_ptr->full.waypoints[i - 1].id;
  mc_new_ptr->full.startingwaypoint = id;
  mc_new_ptr->full.waypointssize = i;
  mc_new_ptr->full.checksum = Checksum((uint8_t*)mc_new_ptr,sizeof(mc_t));
  return true;
}

/* GetMCWaypointSubSequence: Get a mission command prefix if the waypoint being
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
bool GetMCWaypointSubSequence(const mc_t * orig_mc_ptr,
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
      return MCWaypointSubSequence(orig_mc_ptr, ap_id, len, new_mc_ptr);
    }

    it_id = wp.nxid;
  }

  /* Handle the special case where the auto-pilot waypoint lenght is
     1. */
  if( len == 1 ) {
    return MCWaypointSubSequence(orig_mc_ptr, ap_id, len, new_mc_ptr);
  }

  /* assumption: Control flow should never get here. */
  assert(false);
  return false;
}

/* PrintMC: Output the mission command in human readable form for
   debugging purposes. 

     f - The file to read the mission command from.

     mc_ptr - The mission command to print.

*/
void PrintMC(FILE * f, mc_t * mc_ptr) {
  uint16_t i = 0;
  double lat = 0.0;
  double lng = 0.0;
  float alt =  0.0;
  float spd = 0.0;

  /* assumption: mc_ptr is not NULL. */
  assert(mc_ptr != NULL);
  /* assumption: f is not NULL. */
  assert(f != NULL);
  
  fprintf(f,"command id: %lu\n",mc_ptr->full.commandid);
  fprintf(f,"vehicle id: %lu\n",mc_ptr->full.vehicleid);
  fprintf(f,"command status: %u\n",mc_ptr->full.commandstatus);
  fprintf(f,"waypoints: %hu\n",mc_ptr->full.waypointssize);
  for(i = 0 ;i < mc_ptr->full.waypointssize ; i++) {
    memcpy((uint8_t *)&lat,(uint8_t *)&(mc_ptr->full.waypoints[i].latitude),sizeof(double));
    memcpy((uint8_t *)&lng,(uint8_t *)&(mc_ptr->full.waypoints[i].longitude),sizeof(double));
    memcpy((uint8_t *)&alt,(uint8_t *)&(mc_ptr->full.waypoints[i].altitude),sizeof(float));
    memcpy((uint8_t *)&spd,(uint8_t *)&(mc_ptr->full.waypoints[i].speed),sizeof(float));

    fprintf(f,"\t waypoint %hu:\n",i+1);    
    fprintf(f,"\t\tlatitude: %lf\n", lat);
    fprintf(f,"\t\tlongitude: %lf\n", lng);
    fprintf(f,"\t\taltitude: %f\n", alt);
    fprintf(f,"\t\taltitude type: %i\n", mc_ptr->full.waypoints[i].altitude_type);
    fprintf(f,"\t\tid: %lu\n",mc_ptr->full.waypoints[i].id);
    fprintf(f,"\t\tnext id: %lu\n",mc_ptr->full.waypoints[i].nxid);
    fprintf(f,"\t\tspeed:%f\n", spd);
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


#ifdef __MCUTILS_TESTS__

mc_t orig_mc, new_mc, blnk_mc = {};

#define RETURNONFAIL(X)                                                 \
  if((X) != true) {                                                     \
    fprintf(stderr,"(%s:%u) Test failed.\n",__FILE__,__LINE__);         \
    return false;                                                       \
  }

#define TEST(X) \
  {                                                                   \
    bool flag;                                                        \
    fprintf(stdout,"%s ",#X);                                         \
    flag = X();                                                       \
    fprintf(stdout, "%s\n", flag == true ? " Passed." : " Failed.");  \
  }

/*
void PrintMCCData(FILE * f, mc_t * mc_ptr) {
  uint16_t i = 0;

  fprintf(f,"const struct mc_full_struct waterways_c_data = \n\t{{},");    
  fprintf(f,"%lu,",mc_ptr->full.commandid);
  fprintf(f,"%lu,",mc_ptr->full.vehicleid);
  fprintf(f,"%hu,",mc_ptr->full.vehicleactionlistsize);
  fprintf(f,"%u,",mc_ptr->full.commandstatus);
  fprintf(f,"%hu,\n\t\t{",mc_ptr->full.waypointssize);
  for(i = 0 ;i < mc_ptr->full.waypointssize ; i++) {

    fprintf(f,"\n\t\t\t{{},");    
    fprintf(f,"%luLU,",mc_ptr->full.waypoints[i].latitude);
    fprintf(f,"%luLU,", mc_ptr->full.waypoints[i].longitude);
    fprintf(f,"%u,", mc_ptr->full.waypoints[i].altitude);
    fprintf(f,"%i,", mc_ptr->full.waypoints[i].altitude_type);
    fprintf(f,"%lu,",mc_ptr->full.waypoints[i].id);
    fprintf(f,"%lu,",mc_ptr->full.waypoints[i].nxid);
    fprintf(f,"%u,",mc_ptr->full.waypoints[i].speed);
    fprintf(f,"%i,",mc_ptr->full.waypoints[i].speed_type);
    fprintf(f,"%f,",mc_ptr->full.waypoints[i].climbrate);
    fprintf(f,"%i,",mc_ptr->full.waypoints[i].turntype);
    fprintf(f,"%hu,",
            mc_ptr->full.waypoints[i].vehicleactionlistsize);
    fprintf(f,"%lu,",
            mc_ptr->full.waypoints[i].contingencywaypointa);
    fprintf(f,"%lu,",
            mc_ptr->full.waypoints[i].contingencywaypointb);
    fprintf(f,"%hu},",
            mc_ptr->full.waypoints[i].associatedtasksize);
  }
  fprintf(f,"\n\t\t},\n\t%lu,",mc_ptr->full.startingwaypoint);
  fprintf(f,"%u};\n",mc_ptr->full.checksum);
  fflush(f);
  return;
}
*/


bool CheckMCWaypointSubSequence(const mc_t * orig_mc,
                                const mc_t * new_mc,
                                const uint64_t start_waypoint_id,
                                const uint16_t sslen) {
  wp_t orig_wp;
  wp_t new_wp;
  uint64_t it_id = start_waypoint_id;

  /* Certain parts of a mission command subsequence should not change. */
  RETURNONFAIL(memcmp(orig_mc->full.header,
                      new_mc->full.header,
                      MC_HDR_LEN) == 0);
  RETURNONFAIL(orig_mc->full.commandid == new_mc->full.commandid);
  RETURNONFAIL(orig_mc->full.vehicleid == new_mc->full.vehicleid);
  RETURNONFAIL(orig_mc->full.vehicleactionlistsize ==
               new_mc->full.vehicleactionlistsize);

  /* A subsequence could be shorter. */
  RETURNONFAIL(new_mc->full.waypointssize <= sslen);

  /* The starting point we provided to the subsequence should be its
     starting point. */
  RETURNONFAIL(start_waypoint_id == new_mc->full.startingwaypoint);

  /* Check that all non-last waypoints are identical up to the
     subsequence size. */
  for(uint16_t j = 0 ; j < new_mc->full.waypointssize - 1; j++) {
    RETURNONFAIL(FindWP(orig_mc, it_id, &orig_wp));
    RETURNONFAIL(FindWP(new_mc, it_id, &new_wp));
    RETURNONFAIL(memcmp(&orig_wp,&new_wp, sizeof(wp_t)) == 0);
    it_id = new_wp.nxid;
  }

  /* Check that the last waypoint is identical and that its nxid
     points to itself. */
  RETURNONFAIL(FindWP(orig_mc, it_id, &orig_wp));
  RETURNONFAIL(FindWP(new_mc, it_id, &new_wp));
  orig_wp.nxid = orig_wp.id;
  RETURNONFAIL(memcmp(&orig_wp, &new_wp, sizeof(wp_t)) == 0);        
  return true;
}

bool ExhaustiveTest(const uint16_t waypointlen, const uint64_t start_wp_id) {
  wp_t wp;
  uint64_t total_tests = (waypointlen*(waypointlen+1))/2;
  uint64_t ten_percent = total_tests/10;
  uint64_t tests_completed = 0;

  
  /* For each subsequence length less than or equal to the total
     number of waypoints. */
  for(uint16_t i = 2 ; i <= waypointlen ; i++) {
    uint64_t last_subseq_id = start_wp_id;

 
    
    for(uint16_t j = 1 ; j < i ; j++) {
      new_mc = blnk_mc;
      RETURNONFAIL(MCWaypointSubSequence(&orig_mc,
                                         start_wp_id,
                                         i,
                                         &new_mc));
      RETURNONFAIL(CheckMCWaypointSubSequence(&orig_mc,
                                              &new_mc,
                                              start_wp_id,
                                              i));
      
      last_subseq_id = start_wp_id;
      RETURNONFAIL(FindWP(&orig_mc, last_subseq_id, &wp));
      RETURNONFAIL(GetMCWaypointSubSequence(&orig_mc,
                                            last_subseq_id,
                                            wp.id,
                                            i,
                                            &new_mc) != true);

      uint16_t n = 0;    
      for(uint16_t k = 0 ; k < j ; k++) {
        n++;
        RETURNONFAIL(FindWP(&orig_mc, wp.nxid, &wp));
      }
      while(wp.id != wp.nxid) {
        bool flag = GetMCWaypointSubSequence(&orig_mc,
                                             last_subseq_id,
                                             wp.id,
                                             i,
                                             &new_mc);
        if(n < i/2) {
          RETURNONFAIL(flag != true);
        } else {
          n = 0;    
          last_subseq_id = wp.id;
          RETURNONFAIL(flag == true);
          RETURNONFAIL(CheckMCWaypointSubSequence(&orig_mc,
                                                  &new_mc,
                                                  last_subseq_id,
                                                  i));
        }
        for(uint16_t k = 0 ; k < j ; k++) {
          n++;
          RETURNONFAIL(FindWP(&orig_mc, wp.nxid, &wp));
        }
      }
      tests_completed++;
      if(tests_completed % ten_percent == 0) {
        /* Update test progress. */
        fprintf(stdout," %lu0 ",tests_completed / ten_percent);
        fflush(stdout);
      }
    }
  }
  
  return true;
}

#include "testdata/waterways_data.h"
 
bool WaterwaysTestFromFile() {

  FILE * f = NULL;
  const uint64_t start_wp_id = 100004001;
  const uint16_t waypointslen = 76;
  
  orig_mc = blnk_mc;
  
  /* Load waterways data. */
  f = fopen("./testdata/waterways.mc","r");
  RETURNONFAIL(f != NULL);
  RETURNONFAIL(DeserializeMCFromFile(f, &orig_mc));
  fclose(f);

  ExhaustiveTest(waypointslen,start_wp_id);
}

bool WaterwaysTestFromStruct() {

  const uint64_t start_wp_id = 100004001;
  const uint16_t waypointslen = 76;
  
  orig_mc = waterways_data;
  ExhaustiveTest(waypointslen,start_wp_id);
}


int main(void) {
  fprintf(stdout,"%lu\n",sizeof(mc_t));
  //TEST(WaterwaysTestFromFile);
  TEST(WaterwaysTestFromStruct);

  return 0;
}

#endif /* __MCUTILS_TESTS__ */

/******************************************************************************
* Author: Dan DaCosta                                                         *
*                                                                             *
* Purposes: Implements a number of functions useful for mission               *
* command manipulation.                                                       *
*                                                                             *
* Testing build:                                                              *
*   $CC -g -I./ -I./common/ -D__MISSIONCOMMANDUTILS_TESTS__ *.c common/*.c    *
******************************************************************************/

//#include "lmcp.h"
#include "MissionCommandUtils.h"
#include <stdbool.h>

#define AUTOCORRES
#ifdef AUTOCORRES
#define printf(args...) 
#define assert(x)
void *memset(void *s, int c, size_t n);
void *calloc(size_t nmemb, size_t size);
void free(void * p);
#else
#include <assert.h>
#include <stdlib.h>
#endif

#define DEBUG(fmt,args...) \
  printf("%s,%s,%i:"fmt,__FUNCTION__,"MissionCommandMtils.c",__LINE__,##args)


void MCEInit(MissionCommandExt * mce, uint16_t waypoints) {
  memset((uint8_t*)&(mce->missioncommand),0,sizeof(MissionCommand));
  mce->missioncommand.waypointlist = calloc(sizeof(Waypoint*),waypoints);
  mce->waypoints = calloc(sizeof(Waypoint),waypoints);
  for(uint16_t i = 0; i < waypoints; i++) {
    mce->missioncommand.waypointlist[i] = mce->waypoints + i;
  }
  mce->waypointslen = waypoints;
}

Waypoint * FindWP(const MissionCommand * mcp, const int64_t id) {
  uint32_t i;
  /* assumption: p is not NULL. */
  assert(mcp != NULL);

  for(i = 0 ; i < mcp->waypointlist_ai.length; i++) {
    if(mcp->waypointlist[i]->number == id) {
      return mcp->waypointlist[i];
    }
  }
  return NULL;
}

bool MCWaypointSubSequence(const MissionCommand * omcp,
              const int64_t id,
              const uint16_t len,
              MissionCommandExt * wmcep) {
  MissionCommand * wmcp = (MissionCommand*)wmcep;
  uint16_t i;
  Waypoint * wp;
  int64_t idit = id;

  /* assumption: omcp is not NULL. */
  assert(omcp != NULL);
  /* assumption: f is not NULL. */
  assert(wmcp != NULL);

  /* Ensure that a bad id was not provided. */
  wp = FindWP(omcp, idit);
  if(wp == NULL) {
    DEBUG("Waypoint %ld not found.\n",id);
    return false;
  }

  /* Ensure that a 0 length prefix was not asked for. */
  if(len == 0) {
    return false;
  }

  Waypoint ** tmp = wmcp->waypointlist;
  *wmcp = *omcp;
  wmcp->waypointlist = tmp;
  
  for(i=0; i<len ; i++) {

    /* assumption: all ids in the waypoint list can be found. */
    wp = FindWP(omcp, idit);
    assert(wp != NULL);
    wmcep->waypoints[i] = *wp;
    if(wp->number == wp->nextwaypoint) {
      i++;
      break;
    }
    idit = wp->nextwaypoint;
  }
  
  wmcp->waypointlist_ai.length = i;
  wmcp->waypointlist[i - 1]->nextwaypoint = wmcp->waypointlist[i - 1]->number;
  wmcp->firstwaypoint = id;
  return true;
}

bool GetMCWaypointSubSequence(const MissionCommand * omcp,
                 const int64_t last_prefix_start_id,
                 const int64_t ap_id,
                 const uint16_t len,
                 MissionCommandExt * wmcep) {
  uint16_t i;
  Waypoint * wp;
  int64_t it_id = last_prefix_start_id;
  int64_t last_visited_id;
  
  /* assumption: omcp is not NULL. */
  assert(omcp != NULL);

  /* assumption: f is not NULL. */
  assert(wmcep != NULL);

  /* Ensure that a bad last_prefix_start_id was not provided. */
  wp = FindWP(omcp, it_id);
  if(wp == NULL) {
    return false;
  }

  /* Ensure that a bad ap_id was not provided. */
  wp = FindWP(omcp, ap_id);
  if(wp == NULL) {
    return false;
  }

  /* Ensure that a 0 length prefix was not asked for. */
  if(len == 0) {
    return false;
  }

  /* Check to see if the ap_id is in the first half of the auto-pilot
     length. */

  last_visited_id = it_id;
  for(i = 0; i < len/2 ; i++) {


    wp = FindWP(omcp,it_id);
    /* assumption: all ids in the waypoint list can be found. */
    assert(wp != NULL);

    /* If we have found the end or found the nextwp then there is no
       update to be sent to the auto-pilot. */
    if(wp->number == wp->nextwaypoint || wp->number == ap_id) {
      return false;
    }

    last_visited_id = it_id;
    it_id = wp->nextwaypoint;
  }

  // XXX: Assume if we got a waypoint out somewhere in the entire list
  // we will just pick up from there.
  for( ; i < omcp->waypointlist_ai.length; i++) {

    /* assumption: all ids in the waypoint list can be found. */
    wp = FindWP(omcp,it_id);
    assert(wp != NULL );

    /* If we have found the end or found the nextwp then there is no
       update to be sent to the auto-pilot. */
    if(wp->number == wp->nextwaypoint) {
      return false;
    }

    if( wp->number == ap_id ) {
      bool flag = MCWaypointSubSequence(omcp, it_id, len, wmcep);
      wmcep->missioncommand.firstwaypoint = ap_id;
      return flag;
    }
    last_visited_id = it_id;
    it_id = wp->nextwaypoint;
  }

  /* assumption: Control flow should never get here. */
  assert(false);
  return false;
}

#ifdef __MISSIONCOMMANDUTILS_TESTS__

#include <stdio.h>

#define RETURNONFAIL(X)                                 \
  if((X) != true) {                                     \
    printf("(%s:%u) Test failed.\n",__FILE__,__LINE__); \
    return false;                                       \
  }

#define TEST(X)                                             \
  {                                                         \
    bool flag;                                              \
    printf("%s ",#X);                                       \
    flag = X();                                             \
    printf("%s\n", flag == true ? " Passed." : " Failed."); \
  }

/* missioncommandFromFile: Deserialize a mission command reading from a
   file.

     f - The file to read the mission command from.

     mcp - The mission command to be populated from the serialized data.

*/
void missioncommandFromFile(FILE * f, MissionCommand ** mcpp) {

    uint8_t * source = NULL;
    uint8_t * orig_source = NULL;

    size_t size = 0;

    /* assumption: mcpp is not NULL. */
    assert(mcpp != NULL);
    /* assumption: f is not NULL. */
    assert(f != NULL);

    if (fseek(f, 0L, SEEK_END) == 0) {
        /* Get the size of the file. */
        size = ftell(f);
        if (size == -1) {
            /* Error */
        }

        /* Allocate our buffer to that size. */
        source = malloc(sizeof(char) * (size + 1));
        orig_source = source;
        /* Go back to the start of the file. */
        if (fseek(f, 0L, SEEK_SET) != 0) {
            /* Error */
        }

        /* Read the entire file into memory. */
        size_t newlen = fread(source, sizeof(char), size, f);
        if ( ferror( f ) != 0 ) {
            fputs("Error reading file", stderr);
        } else {
            source[newlen++] = '\0'; /* Just to be safe. */
        }

        assert(lmcp_process_msg(&source,size,(lmcp_object**)mcpp) != -1);
        //lmcp_pp(*mcpp);
        free(orig_source);
        source = NULL;
        orig_source = NULL;
    }


    return;
}

bool CheckMCWaypointSubSequence(const MissionCommand * omcp,
                                const MissionCommand * smcp,
                                const int64_t start_waypoint_id,
                                const uint16_t sslen) {
  Waypoint * owp;
  Waypoint * swp;
  Waypoint twp;
  int64_t it_id = start_waypoint_id;

  /* Certain parts of a mission command subsequence should not change. */
  RETURNONFAIL(omcp->super.commandid == smcp->super.commandid);
  RETURNONFAIL(omcp->super.vehicleid == smcp->super.vehicleid);
  RETURNONFAIL(omcp->super.vehicleactionlist_ai.length
               == smcp->super.vehicleactionlist_ai.length);
  for(uint16_t i = 0 ; i < smcp->super.vehicleactionlist_ai.length ; i ++) {
    RETURNONFAIL(omcp->super.vehicleactionlist[i] == smcp->super.vehicleactionlist[i]);
  }
  
  /* A subsequence could be shorter. */
  RETURNONFAIL(smcp->super.vehicleactionlist_ai.length <= sslen );

  /* The starting point we provided to the subsequence should be its
     starting point. */
  RETURNONFAIL(start_waypoint_id == smcp->firstwaypoint);

  /* Check that all non-last waypoints are identical up to the
     subsequence size. */
  uint16_t i = 0;
  for(; i < smcp->waypointlist_ai.length - 1; i++) {
    owp = FindWP(omcp,it_id);
    RETURNONFAIL(owp != NULL);
    swp = FindWP(smcp,it_id);
    RETURNONFAIL(swp != NULL);
    RETURNONFAIL(owp->super.latitude == smcp->waypointlist[i]->super.latitude);
    RETURNONFAIL(owp->super.longitude == smcp->waypointlist[i]->super.longitude);
    RETURNONFAIL(owp->super.altitude == smcp->waypointlist[i]->super.altitude);
    RETURNONFAIL(owp->super.altitudetype == smcp->waypointlist[i]->super.altitudetype);
    RETURNONFAIL(owp->number == smcp->waypointlist[i]->number);
    RETURNONFAIL(owp->nextwaypoint == smcp->waypointlist[i]->nextwaypoint);
    RETURNONFAIL(owp->speed == smcp->waypointlist[i]->speed);
    RETURNONFAIL(owp->speedtype == smcp->waypointlist[i]->speedtype);
    RETURNONFAIL(owp->climbrate == smcp->waypointlist[i]->climbrate);
    RETURNONFAIL(owp->turntype == smcp->waypointlist[i]->turntype);
    RETURNONFAIL(owp->vehicleactionlist == smcp->waypointlist[i]->vehicleactionlist);
    RETURNONFAIL(owp->vehicleactionlist_ai.length == smcp->waypointlist[i]->vehicleactionlist_ai.length);
    RETURNONFAIL(owp->contingencywaypointa == smcp->waypointlist[i]->contingencywaypointa);
    RETURNONFAIL(owp->contingencywaypointb == smcp->waypointlist[i]->contingencywaypointb);
    RETURNONFAIL(owp->associatedtasks == smcp->waypointlist[i]->associatedtasks);
    RETURNONFAIL(owp->associatedtasks_ai.length == smcp->waypointlist[i]->associatedtasks_ai.length);
    it_id = swp->nextwaypoint;
  }
  
  /* Check that the last waypoint is identical and that its nxid
     points to itself. */
  owp = FindWP(omcp,it_id);
  RETURNONFAIL(owp != NULL);
  swp = FindWP(smcp,it_id);
  RETURNONFAIL(swp != NULL);
  RETURNONFAIL(owp->super.latitude == smcp->waypointlist[i]->super.latitude);
  RETURNONFAIL(owp->super.longitude == smcp->waypointlist[i]->super.longitude);
  RETURNONFAIL(owp->super.altitude == smcp->waypointlist[i]->super.altitude);
  RETURNONFAIL(owp->super.altitudetype == smcp->waypointlist[i]->super.altitudetype);
  RETURNONFAIL(owp->number == smcp->waypointlist[i]->number);
  RETURNONFAIL(owp->speed == smcp->waypointlist[i]->speed);
  RETURNONFAIL(owp->speedtype == smcp->waypointlist[i]->speedtype);
  RETURNONFAIL(owp->climbrate == smcp->waypointlist[i]->climbrate);
  RETURNONFAIL(owp->turntype == smcp->waypointlist[i]->turntype);
  RETURNONFAIL(owp->vehicleactionlist == smcp->waypointlist[i]->vehicleactionlist);
  RETURNONFAIL(owp->vehicleactionlist_ai.length == smcp->waypointlist[i]->vehicleactionlist_ai.length);
  RETURNONFAIL(owp->contingencywaypointa == smcp->waypointlist[i]->contingencywaypointa);
  RETURNONFAIL(owp->contingencywaypointb == smcp->waypointlist[i]->contingencywaypointb);
  RETURNONFAIL(owp->associatedtasks == smcp->waypointlist[i]->associatedtasks);
  RETURNONFAIL(owp->associatedtasks_ai.length == smcp->waypointlist[i]->associatedtasks_ai.length);
  return true;
}


bool ExhaustiveTest(MissionCommand * omcp) {
  Waypoint * wp = NULL;
  uint64_t total_tests = (omcp->waypointlist_ai.length*(omcp->waypointlist_ai.length+1))/2;
  uint64_t ten_percent = total_tests/10;
  uint64_t tests_completed = 0;
  MissionCommandExt smce = {};
  MissionCommand * smcp = (MissionCommand*)&smce;

  /* For each subsequence length less than or equal to the total
     number of waypoints. */
  for(uint16_t i = 2 ; i <= omcp->waypointlist_ai.length ; i++) {
    int64_t last_subseq_id = omcp->firstwaypoint;
    MCEInit(&smce,i);

    for(uint16_t j = 1 ; j < i ; j++) {
      RETURNONFAIL(MCWaypointSubSequence(omcp,
                                         omcp->firstwaypoint,
                                         i,
                                         & smce));
      RETURNONFAIL(CheckMCWaypointSubSequence(omcp,
                                              smcp,
                                              omcp->firstwaypoint,
                                              i));

      last_subseq_id = omcp->firstwaypoint;
      wp = FindWP(omcp,last_subseq_id);
      RETURNONFAIL(wp != NULL);
      RETURNONFAIL(GetMCWaypointSubSequence(omcp,
                                            last_subseq_id,
                                            wp->number,
                                            i,
                                            &smce) != true);

      uint16_t c = 0;
      uint16_t n = 0;
      for(uint16_t k = 0 ; k < j ; k++) {
        n++;
        c++;
        wp = FindWP(omcp,wp->nextwaypoint);
        RETURNONFAIL(wp != NULL);
      }
      while(wp->number != wp->nextwaypoint) {
        bool flag = GetMCWaypointSubSequence(omcp,
                                             last_subseq_id,
                                             wp->number,
                                             i,
                                             &smce);
        if(n < i/2) {
          RETURNONFAIL(flag != true);
        } else  {
          n = 0;
          last_subseq_id = wp->number;
          RETURNONFAIL(flag == true);
          RETURNONFAIL(CheckMCWaypointSubSequence(omcp,
                                                  smcp,
                                                  last_subseq_id,
                                                  i));
        }
        for(uint16_t k = 0 ; k < j ; k++) {
          c++;
          n++;
          wp = FindWP(omcp,wp->nextwaypoint);
          RETURNONFAIL(wp != NULL);
        }
      }
      tests_completed++;
      if(tests_completed % ten_percent == 0) {
        /* Update test progress. */
        fprintf(stdout," %lu0 ",tests_completed / ten_percent);
        fflush(stdout);
      }
    }
    free(smce.waypoints);
    smce.waypoints = NULL;
    free(smce.missioncommand.waypointlist);
    smce.missioncommand.waypointlist = NULL;
  }  
  return true;
}

bool WaterwaysTestFromFile() {

    FILE * f = NULL;
    MissionCommand * omcp = NULL;
    lmcp_init_MissionCommand(&omcp);
    /* Load waterways data. */
    f = fopen("./testdata/waterways.mc","r");
    RETURNONFAIL(f != NULL);
    missioncommandFromFile(f, &omcp);
    fclose(f);

    ExhaustiveTest(omcp);

    lmcp_free((lmcp_object*)omcp);
    return true;
}


int main(void) {
    TEST(WaterwaysTestFromFile);

    return 0;
}

#endif /* __MISSIONCOMMANDUTILS_TESTS__ */

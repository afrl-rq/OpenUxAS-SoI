/******************************************************************************
* Author: Dan DaCosta                                                         *
*                                                                             *
* Purposes: Implements a number of functions useful for mission               *
* command manipulation.                                                       *
*                                                                             *
* Testing build:  $CC -g -D__MISSIONCOMMANDUTILS_TESTS__ *.c                  *
******************************************************************************/

#include "lmcp.h"
#include "MissionCommandUtils.h"
#include <assert.h>
#include <string.h>
#include <stdbool.h>

#define DEBUG(fmt,args...) \
  printf("%s,%s,%i:"fmt,__FUNCTION__,"MissionCommandUtils.c",__LINE__,##args)


void MCEInit(MissionCommandExt * mce, uint16_t waypoints) {
  memset((uint8_t*)&(mce->MissionCommand),0,sizeof(MissionCommand));
  mce->MissionCommand.WaypointList = calloc(sizeof(Waypoint*),waypoints);
  mce->Waypoints = calloc(sizeof(Waypoint),waypoints);
  for(uint16_t i = 0; i < waypoints; i++) {
    mce->MissionCommand.WaypointList[i] = mce->Waypoints + i;
  }
  mce->WaypointsLen = waypoints;
}

/* FindWP: Find a waypoint associated with an id.

     mcp - Pointer to a mission command.

     id - Waypoint identifier to be searched for.

     wpp - Pointer to waypoint where found waypoint will be stored.

     returns - True if the waypoint was found, false otherwise.
*/
bool FindWP(const MissionCommand * mcp, const int64_t id, Waypoint ** wpp) {
  uint16_t i;

  /* assumption: p is not NULL. */
  assert(mcp != NULL);
  /* assumption: f is not NULL. */
  assert(wpp != NULL);

  for(i = 0 ; i < mcp->WaypointList_ai.length ; i++) {
    if(mcp->WaypointList[i]->Number == id) {
      *wpp = mcp->WaypointList[i];
      return true;
    }
  }

  return false;
}

/* MCWaypointSubSequence: Create a new mission command from a prefix of the
   waypoints of another mission command.

     omcp - The mission command whose prefix waypoints will be
     used to build a new mission command.

     id - The waypoint id to start the prefix from.

     len - The length of the prefix.

     new_mc_ptr - The mission command that will stored the prefix
     version of mc_orig_ptr.

*/
bool MCWaypointSubSequence(const MissionCommand * omcp,
              const int64_t id,
              const uint16_t len,
              MissionCommandExt * wmcep) {
  MissionCommand * wmcp = (MissionCommand*)wmcep;
  uint16_t i;
  Waypoint * wp = NULL;
  int64_t idit = id;

  /* assumption: omcp is not NULL. */
  assert(omcp != NULL);
  /* assumption: f is not NULL. */
  assert(wmcp != NULL);

  /* Ensure that a bad id was not provided. */
  if(FindWP(omcp, id, &wp) != true) {
    DEBUG("Waypoint %ld not found.\n",id);
    return false;
  }

  /* Ensure that a 0 length prefix was not asked for. */
  if(len == 0) {
    return false;
  }

  Waypoint ** tmp = wmcp->WaypointList;
  *wmcp = *omcp;
  wmcp->WaypointList = tmp;
  
  for(i=0; i<len ; i++) {

    /* assumption: all ids in the waypoint list can be found. */
    assert(FindWP(omcp,idit,&wp) == true);

    wmcep->Waypoints[i] = *wp;
    if(wp->Number == wp->NextWaypoint) {
      i++;
      break;
    }
    idit = wp->NextWaypoint;
  }
  
  wmcp->WaypointList_ai.length = i;
  wmcp->WaypointList[i - 1]->NextWaypoint = wmcp->WaypointList[i - 1]->Number;
  wmcp->FirstWaypoint = id;
  return true;
}

/* GetMCWaypointSubSequence: Get a mission command prefix if the waypoint being
   approached by the platform is half way through the previous mission
   command prefix which was assumed to be sent.

     omcp - The mission command whose prefix waypoints will be
     used to build a new mission command.

     last_prefix_start_id - The starting waypoint id of the last
     prefix sent to the auto-pilot.

     ap_wp - The waypoint the auto-pilot is currently heading towards.

     len - The len of the new prefix.

     wmcp - The storage place of the new prefix mission command.

     returns - True if a new prefix mission command was selected,
     false otherwise.

 */
bool GetMCWaypointSubSequence(const MissionCommand * omcp,
                 const int64_t last_prefix_start_id,
                 const int64_t ap_id,
                 const uint16_t len,
                 MissionCommandExt * wmcep) {
  uint16_t i;
  Waypoint * wp;
  int64_t it_id = last_prefix_start_id;

  /* assumption: omcp is not NULL. */
  assert(omcp != NULL);

  /* assumption: f is not NULL. */
  assert(wmcep != NULL);

  /* Ensure that a bad last_prefix_start_id was not provided. */
  if(FindWP(omcp, last_prefix_start_id, &wp) != true) {
    return false;
  }

  /* Ensure that a bad ap_id was not provided. */
  if(FindWP(omcp, ap_id, &wp) != true) {
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
    assert(FindWP(omcp,it_id,&wp) == true);

    /* If we have found the end or found the nextwp then there is no
       update to be sent to the auto-pilot. */
    if(wp->Number == wp->NextWaypoint || wp->Number == ap_id) {
      return false;
    }

    it_id = wp->NextWaypoint;
  }

  for( ; i < len; i++) {

    /* assumption: all ids in the waypoint list can be found. */
    assert(FindWP(omcp, it_id, &wp) == true );

    /* If we have found the end or found the nextwp then there is no
       update to be sent to the auto-pilot. */
    if(wp->Number == wp->NextWaypoint) {
      return false;
    }

    
    if( wp->Number == ap_id ) {
      return MCWaypointSubSequence(omcp, ap_id, len, wmcep);
    }

    it_id = wp->NextWaypoint;
  }

  /* Handle the special case where the auto-pilot waypoint length is
     1. */
  if( len == 1 ) {
    return MCWaypointSubSequence(omcp, ap_id, len, wmcep);
  }

  /* assumption: Control flow should never get here. */
  assert(false);
  return false;
}

#ifdef __MISSIONCOMMANDUTILS_TESTS__

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

/* MissionCommandFromFile: Deserialize a mission command reading from a
   file.

     f - The file to read the mission command from.

     mcp - The mission command to be populated from the serialized data.

*/
void MissionCommandFromFile(FILE * f, MissionCommand ** mcpp) {

    uint8_t * source = NULL;
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

        /* Go back to the start of the file. */
        if (fseek(f, 0L, SEEK_SET) != 0) {
            /* Error */
        }

        /* Read the entire file into memory. */
        size_t newLen = fread(source, sizeof(char), size, f);
        if ( ferror( f ) != 0 ) {
            fputs("Error reading file", stderr);
        } else {
            source[newLen++] = '\0'; /* Just to be safe. */
        }

        assert(lmcp_process_msg(&source,size,(lmcp_object**)mcpp) != -1);
        free(source);
        source = NULL;
    }


    return;
}

bool CheckMCWaypointSubSequence(const MissionCommand * omcp,
                                const MissionCommand * smcp,
                                const int64_t start_waypoint_id,
                                const uint16_t sslen) {
  Waypoint * owpp;
  Waypoint * swpp;
  Waypoint twp;
  int64_t it_id = start_waypoint_id;

  /* Certain parts of a mission command subsequence should not change. */
  RETURNONFAIL(omcp->super.CommandID == smcp->super.CommandID);
  RETURNONFAIL(omcp->super.VehicleID == smcp->super.VehicleID);
  RETURNONFAIL(omcp->super.VehicleActionList_ai.length
               == smcp->super.VehicleActionList_ai.length);
  for(uint16_t i = 0 ; i < smcp->super.VehicleActionList_ai.length ; i ++) {
    RETURNONFAIL(omcp->super.VehicleActionList[i] == smcp->super.VehicleActionList[i]);
  }
  
  /* A subsequence could be shorter. */
  RETURNONFAIL(smcp->super.VehicleActionList_ai.length <= sslen );

  /* The starting point we provided to the subsequence should be its
     starting point. */
  RETURNONFAIL(start_waypoint_id == smcp->FirstWaypoint);

  /* Check that all non-last waypoints are identical up to the
     subsequence size. */
  uint16_t i = 0;
  for(; i < smcp->WaypointList_ai.length - 1; i++) {
    RETURNONFAIL(FindWP(omcp, it_id, &owpp));
    RETURNONFAIL(FindWP(smcp, it_id, &swpp));
    RETURNONFAIL(owpp->super.Latitude == smcp->WaypointList[i]->super.Latitude);
    RETURNONFAIL(owpp->super.Longitude == smcp->WaypointList[i]->super.Longitude);
    RETURNONFAIL(owpp->super.Altitude == smcp->WaypointList[i]->super.Altitude);
    RETURNONFAIL(owpp->super.AltitudeType == smcp->WaypointList[i]->super.AltitudeType);
    RETURNONFAIL(owpp->Number == smcp->WaypointList[i]->Number);
    RETURNONFAIL(owpp->NextWaypoint == smcp->WaypointList[i]->NextWaypoint);
    RETURNONFAIL(owpp->Speed == smcp->WaypointList[i]->Speed);
    RETURNONFAIL(owpp->SpeedType == smcp->WaypointList[i]->SpeedType);
    RETURNONFAIL(owpp->ClimbRate == smcp->WaypointList[i]->ClimbRate);
    RETURNONFAIL(owpp->TurnType == smcp->WaypointList[i]->TurnType);
    RETURNONFAIL(owpp->VehicleActionList == smcp->WaypointList[i]->VehicleActionList);
    RETURNONFAIL(owpp->VehicleActionList_ai.length == smcp->WaypointList[i]->VehicleActionList_ai.length);
    RETURNONFAIL(owpp->ContingencyWaypointA == smcp->WaypointList[i]->ContingencyWaypointA);
    RETURNONFAIL(owpp->ContingencyWaypointB == smcp->WaypointList[i]->ContingencyWaypointB);
    RETURNONFAIL(owpp->AssociatedTasks == smcp->WaypointList[i]->AssociatedTasks);
    RETURNONFAIL(owpp->AssociatedTasks_ai.length == smcp->WaypointList[i]->AssociatedTasks_ai.length);
    it_id = swpp->NextWaypoint;
  }
  
  /* Check that the last waypoint is identical and that its nxid
     points to itself. */
  RETURNONFAIL(FindWP(omcp, it_id, &owpp));
  RETURNONFAIL(FindWP(smcp, it_id, &swpp));
  RETURNONFAIL(owpp->super.Latitude == smcp->WaypointList[i]->super.Latitude);
  RETURNONFAIL(owpp->super.Longitude == smcp->WaypointList[i]->super.Longitude);
  RETURNONFAIL(owpp->super.Altitude == smcp->WaypointList[i]->super.Altitude);
  RETURNONFAIL(owpp->super.AltitudeType == smcp->WaypointList[i]->super.AltitudeType);
  RETURNONFAIL(owpp->Number == smcp->WaypointList[i]->Number);
  RETURNONFAIL(owpp->Speed == smcp->WaypointList[i]->Speed);
  RETURNONFAIL(owpp->SpeedType == smcp->WaypointList[i]->SpeedType);
  RETURNONFAIL(owpp->ClimbRate == smcp->WaypointList[i]->ClimbRate);
  RETURNONFAIL(owpp->TurnType == smcp->WaypointList[i]->TurnType);
  RETURNONFAIL(owpp->VehicleActionList == smcp->WaypointList[i]->VehicleActionList);
  RETURNONFAIL(owpp->VehicleActionList_ai.length == smcp->WaypointList[i]->VehicleActionList_ai.length);
  RETURNONFAIL(owpp->ContingencyWaypointA == smcp->WaypointList[i]->ContingencyWaypointA);
  RETURNONFAIL(owpp->ContingencyWaypointB == smcp->WaypointList[i]->ContingencyWaypointB);
  RETURNONFAIL(owpp->AssociatedTasks == smcp->WaypointList[i]->AssociatedTasks);
  RETURNONFAIL(owpp->AssociatedTasks_ai.length == smcp->WaypointList[i]->AssociatedTasks_ai.length);
  return true;
}


bool ExhaustiveTest(MissionCommand * omcp) {
  Waypoint * wp = NULL;
  uint64_t total_tests = (omcp->WaypointList_ai.length*(omcp->WaypointList_ai.length+1))/2;
  uint64_t ten_percent = total_tests/10;
  uint64_t tests_completed = 0;
  MissionCommandExt smce = {};
  MissionCommand * smcp = (MissionCommand*)&smce;

  /* For each subsequence length less than or equal to the total
     number of waypoints. */
  for(uint16_t i = 2 ; i <= omcp->WaypointList_ai.length ; i++) {
    int64_t last_subseq_id = omcp->FirstWaypoint;
    MCEInit(&smce,i);

    for(uint16_t j = 1 ; j < i ; j++) {
      RETURNONFAIL(MCWaypointSubSequence(omcp,
                                         omcp->FirstWaypoint,
                                         i,
                                         & smce));
      RETURNONFAIL(CheckMCWaypointSubSequence(omcp,
                                              smcp,
                                              omcp->FirstWaypoint,
                                              i));

      last_subseq_id = omcp->FirstWaypoint;
      RETURNONFAIL(FindWP(omcp, last_subseq_id, &wp));
      RETURNONFAIL(GetMCWaypointSubSequence(omcp,
                                            last_subseq_id,
                                            wp->Number,
                                            i,
                                            &smce) != true);

      uint16_t c = 0;
      uint16_t n = 0;
      for(uint16_t k = 0 ; k < j ; k++) {
        n++;
        c++;
        RETURNONFAIL(FindWP(omcp, wp->NextWaypoint, &wp));
      }
      while(wp->Number != wp->NextWaypoint) {
        bool flag = GetMCWaypointSubSequence(omcp,
                                             last_subseq_id,
                                             wp->Number,
                                             i,
                                             &smce);
        if(n < i/2) {
          RETURNONFAIL(flag != true);
        } else  {
          n = 0;
          last_subseq_id = wp->Number;
          RETURNONFAIL(flag == true);
          RETURNONFAIL(CheckMCWaypointSubSequence(omcp,
                                                  smcp,
                                                  last_subseq_id,
                                                  i));
        }
        for(uint16_t k = 0 ; k < j ; k++) {
          c++;
          n++;
          RETURNONFAIL(FindWP(omcp, wp->NextWaypoint, &wp));
        }
      }
      tests_completed++;
      if(tests_completed % ten_percent == 0) {
        /* Update test progress. */
        fprintf(stdout," %lu0 ",tests_completed / ten_percent);
        fflush(stdout);
      }
    }
    free(smce.Waypoints);
    smce.Waypoints = NULL;
    free(smce.MissionCommand.WaypointList);
    smce.MissionCommand.WaypointList = NULL;
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
    MissionCommandFromFile(f, &omcp);
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

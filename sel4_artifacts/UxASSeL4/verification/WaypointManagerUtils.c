/*
 * Author: Dan DaCosta
 * Company: Rockwell Collins
 * License: Air Force Open Source Agreement Version 1.0
 *
 * Testing build:                                                          
 *   gcc -g -I../CMASI -I../CMASI/common/ -D__WAYPOINTMANAGERUTILS_TESTS__ *.c ../CMASI/*.c ../CMASI/common/*.c -o tests
 *   ./tests
 *   
 */
#include "WaypointManagerUtils.h"
#include <stdbool.h>

int lmcp_process_msg(uint8_t** inb, size_t size, lmcp_object **o);
int lmcp_unpack(uint8_t** inb, size_t size, lmcp_object **o);

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

/* ASM: ws != null */
/* ASM: length > 0 */
Waypoint * FindWaypoint(const Waypoint * ws, const uint16_t len, const int64_t id) {
  for(uint16_t i = 0 ; i < len; i++) {
    if(ws[i].number == id) {
     return ws + i;
    }
  }
  return NULL;
}

/* NB: Cycles in ws will be unrolled into win. */
/* ASM: id can be found in ws. */
/* ASM: All next ids in the ws waypoint list can be found in ws. */
/* ASM: ws != null */
/* ASM: len_ws > 0. */
/* ASM: ws_win != null */
/* ASM: len_ws_win > 0 */
/* ASM: len_ws_win is less than the number of waypoints that can be
   stored in ws_win. */
/* ASM: Last waypoint starts a cycle. */
void FillWindow(  Waypoint * ws
                  , uint16_t len_ws
                  , int64_t id
                  , uint16_t len_ws_win
                  , Waypoint * ws_win /* out */) {
  uint16_t i;
  int64_t nid = id;
  Waypoint * wp = NULL;
  for(i=0; i < len_ws_win; i++) {
    wp = FindWaypoint(ws, len_ws, nid);
    ws_win[i] = *wp;
    nid = ws_win[i].nextwaypoint;    
  }
  /*ws_win[i].nextwaypoint = ws_win[i].number; */
  return;
}

void GroomWindow(uint16_t len_ws_win
                , Waypoint * ws_win /* out */) {
  ws_win[len_ws_win-1].nextwaypoint = ws_win[len_ws_win-1].number;
  return;
}

/* NB: Cycles in ws will be unrolled into win. */
/* ASM: id can be found in ws. */
/* ASM: All next ids in the ws waypoint list can be found in ws. */
/* ASM: ws != null */
/* ASM: len_ws > 0. */
/* ASM: ws_win != null */
/* ASM: len_ws_win > 0 */
/* ASM: len_ws_win is less than the number of waypoints that can be
   stored in ws_win. */
/* ASM: Last waypoint starts a cycle. */
void AutoPilotMissionCommandSegment(  Waypoint * ws
                                      , uint16_t len_ws
                                      , int64_t id
                                      , Waypoint * ws_win /* out */
                                      , uint16_t len_ws_win) {
  FillWindow(ws, len_ws, id, len_ws_win, ws_win);
  GroomWindow(len_ws_win, ws_win);
  return;
}

#ifdef __WAYPOINTMANAGERUTILS_TESTS__
#include <stdio.h>
#include "MissionCommand.h"


#define DEBUG(fmt,args...) \
  printf("%s,%s,%i:"fmt,__FUNCTION__,"MissionCommandMtils.c",__LINE__,##args)


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

bool MissionCommandSegmentCheck(const Waypoint * ws,
                                const uint16_t ws_len,
                                const int64_t start_waypoint_id,
                                const Waypoint * ws_seg,
                                const uint16_t ws_seg_len) {
  Waypoint * owp;
  Waypoint * swp;
  Waypoint twp;
  int64_t it_id = start_waypoint_id;

  /* Check that all non-last waypoints are identical up to the
     subsequence size. */
  uint16_t i = 0;
  for(; i < ws_seg_len - 1; i++) {
    owp = FindWaypoint(ws,ws_len,it_id);
    RETURNONFAIL(owp != NULL);
    swp = FindWaypoint(ws_seg,ws_seg_len,it_id);
    RETURNONFAIL(swp != NULL);
    RETURNONFAIL(owp->super.latitude == swp->super.latitude);
    RETURNONFAIL(owp->super.longitude == swp->super.longitude);
    RETURNONFAIL(owp->super.altitude == swp->super.altitude);
    RETURNONFAIL(owp->super.altitudetype == swp->super.altitudetype);
    RETURNONFAIL(owp->number == swp->number);
    RETURNONFAIL(owp->nextwaypoint == swp->nextwaypoint);
    RETURNONFAIL(owp->speed == swp->speed);
    RETURNONFAIL(owp->speedtype == swp->speedtype);
    RETURNONFAIL(owp->climbrate == swp->climbrate);
    RETURNONFAIL(owp->turntype == swp->turntype);
    RETURNONFAIL(owp->vehicleactionlist == swp->vehicleactionlist);
    RETURNONFAIL(owp->vehicleactionlist_ai.length == swp->vehicleactionlist_ai.length);
    RETURNONFAIL(owp->contingencywaypointa == swp->contingencywaypointa);
    RETURNONFAIL(owp->contingencywaypointb == swp->contingencywaypointb);
    RETURNONFAIL(owp->associatedtasks == swp->associatedtasks);
    RETURNONFAIL(owp->associatedtasks_ai.length == swp->associatedtasks_ai.length);
    it_id = swp->nextwaypoint;
  }
  
  /* Check that the last waypoint is identical and that its nxid
     points to itself. */
  owp = FindWaypoint(ws,ws_len,it_id);
  RETURNONFAIL(owp != NULL);
  swp = FindWaypoint(ws_seg,ws_seg_len,it_id);
  RETURNONFAIL(swp != NULL);
  RETURNONFAIL(owp->super.latitude == swp->super.latitude);
  RETURNONFAIL(owp->super.longitude == swp->super.longitude);
  RETURNONFAIL(owp->super.altitude == swp->super.altitude);
  RETURNONFAIL(owp->super.altitudetype == swp->super.altitudetype);
  RETURNONFAIL(owp->number == swp->number);
  RETURNONFAIL(owp->speed == swp->speed);
  RETURNONFAIL(owp->speedtype == swp->speedtype);
  RETURNONFAIL(owp->climbrate == swp->climbrate);
  RETURNONFAIL(owp->turntype == swp->turntype);
  RETURNONFAIL(owp->vehicleactionlist == swp->vehicleactionlist);
  RETURNONFAIL(owp->vehicleactionlist_ai.length == swp->vehicleactionlist_ai.length);
  RETURNONFAIL(owp->contingencywaypointa == swp->contingencywaypointa);
  RETURNONFAIL(owp->contingencywaypointb == swp->contingencywaypointb);
  RETURNONFAIL(owp->associatedtasks == swp->associatedtasks);
  RETURNONFAIL(owp->associatedtasks_ai.length == swp->associatedtasks_ai.length);
  return true;
}


bool ExhaustiveTest(MissionCommand * omcp) {
  Waypoint * wp = NULL;
  uint64_t total_tests = (omcp->waypointlist_ai.length*(omcp->waypointlist_ai.length+1))/2;
  uint64_t ten_percent = total_tests/10;
  uint64_t tests_completed = 0;
  Waypoint * ws = NULL;
  Waypoint * ws_seg = NULL;
  uint16_t ws_len = 0;
  /* Convert the mission command into an array of waypoints. */
  ws_len = omcp->waypointlist_ai.length;
  ws = calloc(sizeof(Waypoint),ws_len);
  for(uint16_t i = 0; i < ws_len; i++) {
    ws[i] = *(omcp->waypointlist[i]);
  }
  
  
  /* For each subsequence length less than or equal to the total
     number of waypoints. */
  for(uint16_t i = 2 ; i <= omcp->waypointlist_ai.length ; i++) {
    int64_t last_subseq_id = omcp->firstwaypoint;
    ws_seg = calloc(sizeof(Waypoint),i);        
    for(uint16_t j = 1 ; j < i ; j++) {
      AutoPilotMissionCommandSegment(ws,
                                     ws_len,
                                     omcp->firstwaypoint,
                                     ws_seg,
                                     i);
      RETURNONFAIL(MissionCommandSegmentCheck(ws,
                                              ws_len,
                                              omcp->firstwaypoint,
                                              ws_seg,
                                              i));

      last_subseq_id = omcp->firstwaypoint;
      wp = FindWaypoint(ws,ws_len,last_subseq_id);
      RETURNONFAIL(wp != NULL);
      AutoPilotMissionCommandSegment(ws,
                               ws_len,
                               wp->number,
                               ws_seg,
                               i);      

      uint16_t c = 0;
      uint16_t n = 0;
      for(uint16_t k = 0 ; k < j ; k++) {
        n++;
        c++;
        wp = FindWaypoint(ws,ws_len,wp->nextwaypoint);
        RETURNONFAIL(wp != NULL);
      }
      while(wp->number != wp->nextwaypoint) {
        AutoPilotMissionCommandSegment(ws,
                                       ws_len,
                                       wp->number,
                                       ws_seg,
                                       i);
        RETURNONFAIL(MissionCommandSegmentCheck(ws,
                                                ws_len,
                                                wp->number,
                                                ws_seg,
                                                i));
        for(uint16_t k = 0 ; k < j ; k++) {
          c++;
          n++;
          wp = FindWaypoint(ws, ws_len,wp->nextwaypoint);
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
    free(ws_seg);
    ws_seg = NULL;
  }
  free(ws);
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

#endif /* __WAYPOINTMANAGERUTILS_TESTS__ */

#ifndef __MISSIONCOMMANDUTILS_H__
#define __MISSIONCOMMANDUTILS_H__
#include <stdbool.h>
/*#include "MissionCommand.h"*/
#include "Waypoint.h"

int lmcp_process_msg(uint8_t** inb, size_t size, lmcp_object **o);
int lmcp_unpack(uint8_t** inb, size_t size, lmcp_object **o);


/*struct MissionCommandExt_struct{
  MissionCommand missioncommand;
  Waypoint * waypoints;
  uint16_t waypointslen;

};

typedef struct MissionCommandExt_struct MissionCommandExt; 

void MCEInit(MissionCommandExt * mce, uint16_t waypoints);*/
Waypoint * FindWP(Waypoint * ws, uint16_t len, int64_t id);
void MCWaypointSubSequence(  Waypoint * ws
                           , uint16_t len_ws
                           , int64_t id
                           , uint16_t len_ws_win
                             , Waypoint * ws_win /* out */);
bool GetMCWaypointSubSequence( Waypoint * ws
                             , uint16_t len_ws
                             , int64_t last_start_id
                             , int64_t approach_id
                             , uint16_t len_ws_win
                               , Waypoint * ws_win /* out */ );
#endif /* __MISSIONCOMMANDUTILS_H__ */

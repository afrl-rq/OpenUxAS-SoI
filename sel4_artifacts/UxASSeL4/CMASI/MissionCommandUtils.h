#ifndef __MISSIONCOMMANDUTILS_H__
#define __MISSIONCOMMANDUTILS_H__
#include <stdbool.h>
#include "MissionCommand.h"

int lmcp_process_msg(uint8_t** inb, size_t size, lmcp_object **o);
int lmcp_unpack(uint8_t** inb, size_t size, lmcp_object **o);


struct MissionCommandExt_struct{
  MissionCommand missioncommand;
  Waypoint * waypoints;
  uint16_t waypointslen;

};

typedef struct MissionCommandExt_struct MissionCommandExt;

void MCEInit(MissionCommandExt * mce, uint16_t waypoints);
bool MCWaypointSubSequence(const MissionCommand * omcp,
                           const int64_t id,
                           const uint16_t len,
                           MissionCommandExt * wmcp);
bool GetMCWaypointSubSequence(const MissionCommand * omcp,
                              const int64_t last_prefix_start_id,
                              const int64_t ap_id,
                              const uint16_t len,
                              MissionCommandExt * wmcp);

#endif /* __MISSIONCOMMANDUTILS_H__ */

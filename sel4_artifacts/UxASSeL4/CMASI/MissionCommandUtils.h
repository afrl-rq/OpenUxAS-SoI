#ifndef __MISSIONCOMMANDUTILS_H__
#define __MISSIONCOMMANDUTILS_H__
#include "lmcp.h"
#include <stdbool.h>

typedef
struct {
  MissionCommand MissionCommand;
  Waypoint * Waypoints;
  uint16_t WaypointsLen;

} MissionCommandExt;

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

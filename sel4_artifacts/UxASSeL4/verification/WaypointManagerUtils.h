/*
 * Author: Dan DaCosta
 * Company: Rockwell Collins
 * License: Air Force Open Source Agreement Version 1.0
 *
 * Terminology: 
 *
 *  waypoint - Largely self-explanatory. We are only really using the number
 *  and nextwaypoint field in this data structure.
 *
 *  mission command - An array of unordered Waypoint data
 *  structures.
 *
 *  mission command segment - An array of unordered Waypoint data
 *  structure which is a subset of a mission command.
 *   
 */
#ifndef __WAYPOINTMANAGERUTILS_H__
#define __WAYPOINTMANAGERUTILS_H__
#include <stdbool.h>
#include "../CMASI/Waypoint.h"

bool AutoPilotMissionCommandSegment( Waypoint * ws /* mission
                                                      command. */
                                     , uint16_t len_ws /* mission
                                                          command
                                                          length. */
                                     , int64_t id /* starting ID for
                                                     mission command
                                                     segment. */
                                     , Waypoint * ws_win /* mission
                                                            command
                                                            segment */ /* out */
                                     , uint16_t len_ws_win /* mission
                                                              command
                                                              segment
                                                              length */
                                     );
#endif /* __WAYPOINTMANAGERUTILS_H__ */

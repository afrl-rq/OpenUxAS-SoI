// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "Dpss.h"

//============================================

//  The following functions mirror the once above for the DPSS class. These provide a C style calling mechanism
//  for use with dllimports and exports. Parameter descriptions are the same except for the Dpss* instance parameter.
//  This allows the C style calls to work with the DPSS class.
//
//  THESE FUNCTION SHOULD NOT BE MODIFIED
//

DPSS_API Dpss* CreateDpss()
{
  return new Dpss;
}

DPSS_API void DestroyDpss(Dpss* instance)
{
  delete instance;
}

DPSS_API void SmoothPath(Dpss* instance, DpssWaypoint pathPoints[], int numPoints, SmoothPathInput* spi, DpssWaypoint* outputPoints, int* numOutputPoints)
{
  instance->SmoothPath(pathPoints, numPoints, spi, outputPoints, numOutputPoints); 
}

DPSS_API void SetObjective(Dpss* instance, DpssWaypoint pathPoints[], int numPathPoints, DpssWaypoint planPoints[], int numPlanPoints, ObjectiveParameters* op)
{
  instance->SetObjective(pathPoints, numPathPoints, planPoints, numPlanPoints, op);
}

DPSS_API int AddVehicles(Dpss* instance, int vehicleIds[], int numVehicles)
{
  return instance->AddVehicles(vehicleIds, numVehicles);
}

DPSS_API int RemoveVehicles(Dpss* instance, int vehicleIds[], int numVehicles)
{
  return instance->RemoveVehicles(vehicleIds, numVehicles);
}

DPSS_API void UpdateVehicleTelemetry(Dpss* instance, VehicleTelemetry telemetry)
{
  instance->UpdateVehicleTelemetry(telemetry);
}

DPSS_API void UpdateDpss(Dpss* instance, 
                         VehiclePoint sensorPoints[], int* numSensorPoints, 
                         VehicleGoToPoint vehicleGotoPoints[], int* numGotoPoints, 
                         VehiclePoint turnPoints[], int* numTurnPoints)
{
  instance->UpdateDpss(sensorPoints, numSensorPoints, 
                       vehicleGotoPoints, numGotoPoints, 
                       turnPoints, numTurnPoints);
}

DPSS_API void SetOutputPath(Dpss* instance, const char* path)
{
  instance->SetOutputPath(path);
}

DPSS_API void SetLostCommWaypointNumber(Dpss* instance, unsigned short lostCommWaypointNumber)
{
  instance->SetLostCommWaypointNumber(lostCommWaypointNumber);
}

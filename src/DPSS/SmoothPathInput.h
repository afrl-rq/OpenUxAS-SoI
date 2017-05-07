// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#pragma once
#include "DpssDefs.h"
extern "C"
{
  struct DPSS_API SmoothPathInput
  {
    unsigned int sameSide;
    unsigned int roughPlan;
    unsigned int maxWaypoints;
    unsigned int useTerrainFollowing;
    double cameraAzimuthInRadians;
    double cameraElevationInRadians;
    double nominalAltitudeInMeters;
    double maxCommRangeInMeters;
    double lostCommPointLatitudeInRadians;
    double lostCommPointLongitudeInRadians;

  };
}

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
  struct DPSS_API ObjectiveParameters
  {
    unsigned int sameSide;
    double nominalAzimuthInRadians;
    double nominalElevationInRadians;
    double lreLatitudeInRadians;
    double lreLongitudeInRadians;
    double nearWaypointThresholdDistanceInMeters;
    double reverseManeuverDistanceInMeters;
    double rendezvousDistanceInMeters;
  };

}
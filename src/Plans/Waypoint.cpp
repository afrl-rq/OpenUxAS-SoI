// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// Waypoint.cpp: implementation of the CWaypoint class.
//
//////////////////////////////////////////////////////////////////////

#include "Waypoint.h"

namespace n_FrameworkLib
{

void CWaypoint::osStreamWaypointHeadings(ostream &os) 
{
        os    << "'North_m',\t"
            << "'East_m',\t"
            << "'Altitude_m',\t"
            << "'Speed_mps',\t"
            << "'MachCommandFlag',\t"
            << "'SegmentLength',\t"
            << "'TurnCenterNorth_m',\t"
            << "'TurnCenterEast_m',\t"
            << "'TurnDirection',\t"
            << "'WaypointType',\t"
            << "'ObjectiveID',\t"
            << "'ResetVehiclePosition',\t"
            << "'ObjectiveDesiredDirection_rad',\t"
            << "'ObjectiveDesiredStandOff_m'\t";
    }


ostream &operator << (ostream &os,const CWaypoint& wayRhs) 
{
        os    << wayRhs.m_north_m << ",\t"
            << wayRhs.m_east_m << ",\t"
            << wayRhs.m_altitude_m << ",\t"
            << wayRhs.dGetSpeed_mps() << ",\t"
            << wayRhs.bGetMachCommandFlag() << ",\t"
            << wayRhs.dGetSegmentLength() << ",\t"
            << wayRhs.circleGetTurn().m_north_m << ",\t"
            << wayRhs.circleGetTurn().m_east_m << ",\t"
            << (int)wayRhs.circleGetTurn().turnGetTurnDirection() << ",\t"
            << (int)wayRhs.typeGetWaypoint() << ",\t"
            << wayRhs.iGetObjectiveID() << ",\t"
            << wayRhs.bGetResetVehiclePosition() << ",\t"
            << wayRhs.dGetObjectiveDesiredDirection_rad() << ",\t"
            << wayRhs.dGetObjectiveDesiredStandOff_m() << ",\t";
        return os;
}

#ifdef USE_LAT_LONGS_FROM_WAYPOINTS
uxas::common::utilities::CUnitConversions CWaypointSmall::m_UnitConversions;
#endif    //#ifdef USE_LAT_LONGS_FROM_WAYPOINTS


};      //namespace n_FrameworkLib

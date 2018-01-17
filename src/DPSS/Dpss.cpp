// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "Dpss.h"
using namespace std;

Dpss::Dpss()
{
    // set reasonable default values for system parameters
    m_RendezvousDistance = 1000;     // meters
    m_ReverseManeuverDistance = 100; // meters
    m_NearWpThreshold = 100;         // meters
    m_LostCommWaypointNumber = 255;
    m_LostCommRedirectNumber = 0;

    m_MaxCommunicationRange = 10000;  // meters

    m_NominalAzimuth = 0;             // rad
    m_NominalElevation = dPi/2;       // rad
    m_NominalAltitudeInMeters = 250;  // meters
    m_SameSidePlan = 0;
    m_ReturnPlanWpIndex = -1;
    m_SingleDirectionPlan = false;
    m_TerrainFollowing = true;

    m_ForwardPlanLength = 0;          // meters
    m_ReversePlanLength = 0;          // meters
    m_TrueRoadLength = 0;             // meters
    m_EqualDistanceWeight = 0;

    m_OutputPath = "";

}

Dpss::~Dpss()
{
  
}

void Dpss::SmoothPath(DpssWaypoint pathPoints[], int numPoints, SmoothPathInput* spi, DpssWaypoint* outputPoints, int* numOutputPoints)
{
    // handle nonsense input
    if( pathPoints == NULL ) return;
    if( spi == NULL) return;
    if( outputPoints == NULL ) return;
    if( numOutputPoints == NULL ) return;
    if( numPoints <= 0 ) return;
    if( (spi->maxWaypoints) <= 0 ) return;

    // camera angles
    m_NominalElevation = fabs(spi->cameraElevationInRadians); // positive down (can only go down)
    m_NominalAzimuth = spi->cameraAzimuthInRadians;           // positive is from north to east
    m_NominalAltitudeInMeters = fabs(spi->nominalAltitudeInMeters);

    // same side planning
    m_SameSidePlan = (spi->sameSide)?1:0;

    // terrain following
    m_TerrainFollowing = (spi->useTerrainFollowing)?true:false;

    // lost comm point
    m_LostCommPointLatitudeInRadians = spi->lostCommPointLatitudeInRadians;
    m_LostCommPointLongitudeInRadians = spi->lostCommPointLongitudeInRadians;

    // max comm range
    m_MaxCommunicationRange = spi->maxCommRangeInMeters;

    // translate lat/lon to x-y plane
    vector<xyPoint> xyPoints;
    PreProcessPath(pathPoints,numPoints,xyPoints);

    // at this point, only "relevant" points are on the path
    // if we still don't have enough waypoints to represent the
    // road at this level of fidelity, then further pruning is needed
    
    if( (spi->maxWaypoints)/2 < xyPoints.size() )
    {
        if(spi->roughPlan)
            PlanQuickly(xyPoints, (spi->maxWaypoints)/2);
#ifdef AFRL_INTERNAL_ENABLED
//        else
//            PlanPrecisely(xyPoints, (spi->maxWaypoints)/2);
#endif
    }
    
    vector<xyPoint> forwardPlan;
    vector<xyPoint> reversePlan;

    OffsetPlanForward(xyPoints,forwardPlan);
    //PostProcessPlan(forwardPlan,50.0);

    OffsetPlanReverse(xyPoints,reversePlan);
    //PostProcessPlan(reversePlan,50.0);

    CombinePlans(forwardPlan, reversePlan, outputPoints, numOutputPoints);
}

void Dpss::SetObjective(DpssWaypoint pathPoints[], int numPathPoints, 
                        DpssWaypoint planPoints[], int numPlanPoints,
                        ObjectiveParameters* op)
{
    int k;
 
    // handle nonsense input
    if( pathPoints == NULL ) return;
    if( numPathPoints <= 0 ) return;
    if( planPoints == NULL ) return;
    if( numPlanPoints <= 0 ) return;
    if( op == NULL ) return;
    
    // update paramters
    m_LreLatitudeInRadians = op->lreLatitudeInRadians;
    m_LreLongitudeInRadians = op->lreLongitudeInRadians;
    m_NearWpThreshold = op->nearWaypointThresholdDistanceInMeters;
    m_NominalAzimuth = op->nominalAzimuthInRadians;
    m_NominalElevation = fabs(op->nominalElevationInRadians);
    m_RendezvousDistance = op->rendezvousDistanceInMeters;
    m_ReverseManeuverDistance = op->reverseManeuverDistanceInMeters;
    m_SameSidePlan = (op->sameSide)?1:0;

    UpdateLinearization(planPoints, numPlanPoints);
    m_FlatEarthConverter.ConvertLatLong_radToNorthEast_m(m_LostCommPointLatitudeInRadians, m_LostCommPointLongitudeInRadians, m_LostCommPoint.y, m_LostCommPoint.x);

    // clear everything out
    m_TrueWaypoints.clear();
    m_LatLonWaypoints.clear();
    m_WpIDList.clear();
    m_TrueRoad.clear();
    m_LatLonRoad.clear();

    // translate lat/lon to x-y plane
    for(k=0; k<numPathPoints; k++)
    {
        m_LatLonRoad.push_back( pathPoints[k] );
        xyPoint pt;
        m_FlatEarthConverter.ConvertLatLong_radToNorthEast_m(pathPoints[k].latitudeInRadians, pathPoints[k].longitudeInRadians, pt.y, pt.x);
        pt.z = pathPoints[k].altitudeInMeters;
        m_TrueRoad.push_back(pt);
    }
    //RemoveRoadPointsOutOfCommRange(m_TrueRoad);

    // translate lat/lon to x-y plane
    for(k=0; k<numPlanPoints; k++)
    {
        if(planPoints[k].waypointNumber != m_LostCommWaypointNumber)
        {
            m_LatLonWaypoints.push_back( planPoints[k] );
            xyPoint pt;
            m_FlatEarthConverter.ConvertLatLong_radToNorthEast_m(planPoints[k].latitudeInRadians, planPoints[k].longitudeInRadians, pt.y, pt.x);
            pt.z = planPoints[k].altitudeInMeters;
            m_TrueWaypoints.push_back(pt);
            m_WpIDList.push_back( planPoints[k].waypointNumber );
        }
    }

    CalculateWpToRdIndexMap();

}

void Dpss::SetObjective(std::vector<xyPoint>& path, std::vector<xyPoint>& plan,    ObjectiveParameters* op)
{ 
    // handle nonsense input
    if( path.empty() ) return;
    if( plan.empty() ) return;
    if( op == NULL ) return;
    
    // update paramters
    m_LreLatitudeInRadians = op->lreLatitudeInRadians;
    m_LreLongitudeInRadians = op->lreLongitudeInRadians;
    m_NearWpThreshold = op->nearWaypointThresholdDistanceInMeters;
    m_NominalAzimuth = op->nominalAzimuthInRadians;
    m_NominalElevation = fabs(op->nominalElevationInRadians);
    m_RendezvousDistance = op->rendezvousDistanceInMeters;
    m_ReverseManeuverDistance = op->reverseManeuverDistanceInMeters;
    m_SameSidePlan = (op->sameSide)?1:0;

    // clear everything out
    m_TrueWaypoints.clear();
    m_LatLonWaypoints.clear();
    m_WpIDList.clear();
    m_TrueRoad.clear();
    m_LatLonRoad.clear();

    m_TrueRoad.assign(path.begin(), path.end());
    m_TrueWaypoints.assign(plan.begin(), plan.end());
    m_WpIDList.assign(plan.size(),0);
    for(int k=0; k<(int) m_WpIDList.size(); k++)
        m_WpIDList[k] = k;

    CalculateWpToRdIndexMap();

}

int Dpss::AddVehicles(int vehicleIds[], int numVehicles)
{
    for(int k=0; k<numVehicles; k++)
    {
        bool alreadyInTeam = false;
        for(int i=0; i<(int)m_TeamList.size(); i++)
        {
            if(m_TeamList[i] == vehicleIds[k])
                alreadyInTeam = true;
        }
        if( !alreadyInTeam )
            m_TeamList.push_back(vehicleIds[k]);
    }

    return (int) m_TeamList.size(); //return updated vehicle count here
}

int Dpss::RemoveVehicles(int vehicleIds[], int numVehicles)
{
    for(int k=0; k<numVehicles; k++)
    {
        vector<int>::iterator removeThis;
        bool remove = false;
        for(vector<int>::iterator i = m_TeamList.begin(); i != m_TeamList.end(); i++)
        {
            if( vehicleIds[k] == (*i) )
            {
                removeThis = i;
                remove = true;
            }
        }

        if(remove)
            m_TeamList.erase(removeThis);
    }

    return (int) m_TeamList.size(); //return updated vehicle count here
}

void Dpss::UpdateVehicleTelemetry(VehicleTelemetry telemetry)
{
    bool updated = false;
    for(int k=0; k<(int)m_LatLonTeamTelemetry.size(); k++)
    {
        if(m_LatLonTeamTelemetry[k].vehicleId == telemetry.vehicleId)
        {
            // Deep copy of input telemetry to team-list telemetry
            m_LatLonTeamTelemetry[k].altitudeInMeters = telemetry.altitudeInMeters;
            m_LatLonTeamTelemetry[k].latitudeInRadians = telemetry.latitudeInRadians;
            m_LatLonTeamTelemetry[k].longitudeInRadians = telemetry.longitudeInRadians;
            m_LatLonTeamTelemetry[k].toWaypointNumber = telemetry.toWaypointNumber;
            m_LatLonTeamTelemetry[k].fromWaypointNumber = telemetry.fromWaypointNumber;
            m_LatLonTeamTelemetry[k].airSpeedInMps = telemetry.airSpeedInMps;
            m_LatLonTeamTelemetry[k].headingInRadians = telemetry.headingInRadians;
            m_LatLonTeamTelemetry[k].uWindNorthInMps = telemetry.uWindNorthInMps;
            m_LatLonTeamTelemetry[k].vWindEastInMps = telemetry.vWindEastInMps;
            m_LatLonTeamTelemetry[k].commandedAirspeedInMps = telemetry.commandedAirspeedInMps;
            m_LatLonTeamTelemetry[k].commandedAltitudeInMeters = telemetry.commandedAltitudeInMeters;
            m_LatLonTeamTelemetry[k].energyRemaining = telemetry.energyRemaining;
            updated = true;
        }
    }

    if(!updated)
    {
        m_LatLonTeamTelemetry.push_back( telemetry );
    }
}


void Dpss::UpdateDpss(VehiclePoint sensorPoints[], int* numSensorPoints, 
                      VehicleGoToPoint vehicleGotoPoints[], int* numGotoPoints, 
                      VehiclePoint turnPoints[], int* numTurnPoints)
{
    // handle nonsense input
    if( sensorPoints == NULL ) return;
    if( vehicleGotoPoints == NULL) return;
    if( turnPoints == NULL) return;
    if( numSensorPoints == NULL ) return;
    if( numGotoPoints == NULL ) return;
    if( numTurnPoints == NULL ) return;

    if( (*numSensorPoints) < (int)m_TeamList.size() ) return;
    if( (*numGotoPoints) < (int)m_TeamList.size() ) return;
    if( (*numTurnPoints) < (int)m_TeamList.size() ) return;

    // Currently ignores communication constraints, Dpss State, and fuel constraints

    // calculate camera stare point
    for(int k=0; k<(int)m_TeamList.size(); k++)
    {
        int telemIndex = -1;
        for(int j=0; j<(int)m_LatLonTeamTelemetry.size(); j++)
            if(m_TeamList[k] == m_LatLonTeamTelemetry[j].vehicleId)
                telemIndex = j;
        if(telemIndex >= 0)
        {
            CalculateStarePoint(sensorPoints[k],m_LatLonTeamTelemetry[telemIndex]);
            //if(m_LatLonTeamTelemetry[telemIndex].toWaypointNumber == m_LostCommWaypointNumber)
            //{
            //}
        }
        else
        {
            sensorPoints[k].altitudeInMeters = -1.0;
            sensorPoints[k].latitudeInRadians = -1.0;
            sensorPoints[k].longitudeInRadians = -1.0;
            sensorPoints[k].vehicleId = m_TeamList[k];
        }
    }
    (*numSensorPoints) = (int) m_TeamList.size();

    // redirect UAVs that are headed to lost comm waypoint
    for(int k=0; k<(int)m_TeamList.size(); k++)
    {
        int telemIndex = -1;
        for(int j=0; j<(int)m_LatLonTeamTelemetry.size(); j++)
            if(m_TeamList[k] == m_LatLonTeamTelemetry[j].vehicleId)
                telemIndex = j;
        if(telemIndex >= 0)
        {
            if(m_LatLonTeamTelemetry[telemIndex].toWaypointNumber == m_LostCommWaypointNumber)
            {
                bool algorithmRedirected = false;
                for(int n=0; n<(*numGotoPoints); n++)
                {
                    if(vehicleGotoPoints[n].vehicleId == m_LatLonTeamTelemetry[telemIndex].vehicleId)
                        algorithmRedirected = true;
                }
                if(!algorithmRedirected)
                {
                    vehicleGotoPoints[(*numGotoPoints)].vehicleId = m_LatLonTeamTelemetry[telemIndex].vehicleId;
                    vehicleGotoPoints[(*numGotoPoints)].waypointNumber = (unsigned short) m_WpIDList[m_LostCommRedirectNumber];
                    (*numGotoPoints) = (*numGotoPoints) + 1;
                }
            }
        }
    }

}

void Dpss::SetOutputPath(const char* path)
{
  m_OutputPath = path;
}

void Dpss::SetLostCommWaypointNumber(unsigned short lostCommWaypointNumber)
{
    m_LostCommWaypointNumber = lostCommWaypointNumber;
}


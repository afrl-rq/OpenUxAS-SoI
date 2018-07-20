// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================


/* 
 * File:   SensorSteering.cpp
 * Author: steve, derek
 * 
 * Created on May 21, 2018, 10:06 AM
 */

#include "SensorSteering.h"
#include "UxAS_Log.h"



#include <iostream>
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<<>>  SensorSteering:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << "  <<<>>>" << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<<>>  SensorSteering:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << "  <<<>>>" << std::endl;std::cerr.flush();
#define COUT_MSG(MESSAGE) std::cout << "<<>>  SensorSteering:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << "  <<<>>>" << std::endl;std::cout.flush();
#define COUT_DEBUG() std::cout << "<<>>  SensorSteering:" << __FILE__ << ":" << __LINE__ << "  <<<>>>" << std::endl;std::cout.flush();

namespace uxas
{
namespace common
{
namespace utilities
{

void SensorSteering::Initialize(std::vector<std::shared_ptr<PointData> >& waypoints,std::vector<std::shared_ptr<PointData> >& roadpoints)
{
    // 1) find normalized distance of each waypoint in the plan
    m_waypointsLength_m = 0.0;
    m_idVsWaypoint.clear();
    m_roadLength_m = 0.0;
    m_normFactorVsRoadpoint.clear();
   
    std::shared_ptr<PointData> lastPoint;
    for(auto& waypoint : waypoints)
    {
        if(lastPoint)
        {
            m_waypointsLength_m += lastPoint->m_point->relativeDistance2D_m(*(waypoint->m_point));
            waypoint->m_cumulativeDistance_m = m_waypointsLength_m;
        }
        else
        {
            waypoint->m_cumulativeDistance_m = 0.0;
        }
        m_idVsWaypoint[waypoint->m_id] = waypoint;
        lastPoint = waypoint;
    }
       
    // 2) find normalized distance of each road point in the road
    lastPoint.reset();
    for(auto& roadpoint : roadpoints)
    {
        if(lastPoint)
        {
            m_roadLength_m += lastPoint->m_point->relativeDistance2D_m(*(roadpoint->m_point));
            roadpoint->m_cumulativeDistance_m = m_roadLength_m;
        }
        lastPoint = roadpoint;
    }
       
    for(auto& roadpoint : roadpoints)
    {
        int64_t normalizationFactor{0};
        if(m_roadLength_m > 0.0)
        {
            normalizationFactor = static_cast<int64_t>((roadpoint->m_cumulativeDistance_m / m_roadLength_m) * 1000.0);
        }
        m_normFactorVsRoadpoint[normalizationFactor] = roadpoint;
    }
}

void SensorSteering::FindSensorStarePoint(const int64_t& waypointNumber, const afrl::cmasi::Location3D* currentLocation, afrl::cmasi::Location3D& sensorStarePoint,uxas::common::utilities::FlatEarth& flatEarth)
{
    auto itWaypoint = m_idVsWaypoint.find(waypointNumber);
    if(itWaypoint != m_idVsWaypoint.end())
    {
        int64_t normalizationFactor{0};  //default to the first waypoint
        
        if(itWaypoint != m_idVsWaypoint.begin())
        {
            auto itFirstWaypoint = itWaypoint;
            itFirstWaypoint--;
            // find the closest point on the line segment to the position
            
            n_FrameworkLib::CPosition currentPoint(n_Const::c_Convert::toRadians(currentLocation->getLatitude()),
                                                    n_Const::c_Convert::toRadians(currentLocation->getLongitude()),currentLocation->getAltitude(),flatEarth);
                    
            auto AB = *(itWaypoint->second->m_point) - *(itFirstWaypoint->second->m_point);
            auto AP = currentPoint - *(itFirstWaypoint->second->m_point);
            float lengthSqrAB = AB.m_north_m * AB.m_north_m + AB.m_east_m * AB.m_east_m;
            float factor = (AP.m_north_m * AB.m_north_m + AP.m_east_m * AB.m_east_m) / lengthSqrAB;           
            factor = (factor < 0.0)?(0.0):((factor>1.0)?(1.0):(factor));                    
            auto positionDistance_m = factor * (itWaypoint->second->m_cumulativeDistance_m - itFirstWaypoint->second->m_cumulativeDistance_m) +
                                itFirstWaypoint->second->m_cumulativeDistance_m;            
            normalizationFactor = (m_waypointsLength_m>0.0)?( static_cast<int64_t>((positionDistance_m/m_waypointsLength_m) * 1000.0)):(1000);
        }
        double stareLatitude_deg(0.0);
        double stareLongitude_deg(0.0);
        auto rangePair = m_normFactorVsRoadpoint.equal_range(normalizationFactor);
        if(rangePair.first != m_normFactorVsRoadpoint.end())
        {
            if(rangePair.first == m_normFactorVsRoadpoint.begin())
            {
                // point to the first road point
                flatEarth.ConvertNorthEast_mToLatLong_deg(rangePair.first->second->m_point->m_north_m,rangePair.first->second->m_point->m_east_m,stareLatitude_deg,stareLongitude_deg);                
            }
            else
            {
                // found the interval
                auto firstPoint = rangePair.first;
                firstPoint--;
                //assert(normalizationFactor >= firstPoint->first)
                //assert(normalizationFactor <= rangePair.first->first)
                double deltaNorm = static_cast<double>(rangePair.first->first - firstPoint->first);
                double newNorm = static_cast<double>(normalizationFactor - firstPoint->first);
                double fraction = (deltaNorm>0.0)?((newNorm)/(deltaNorm)):(0.0);
                auto starePoint = ((*(rangePair.first->second->m_point) - *(firstPoint->second->m_point))*fraction) + *(firstPoint->second->m_point);
                sensorStarePoint.setAltitude(starePoint.m_altitude_m);
                flatEarth.ConvertNorthEast_mToLatLong_deg(starePoint.m_north_m,starePoint.m_east_m,stareLatitude_deg,stareLongitude_deg);                                
            }
        }
        else
        {
            UXAS_LOG_ERROR("SensorSteering::FindSensorPointingPosition::", " Can not point sensor. waypoint number [" , waypointNumber , "], normalizationFactor[" , normalizationFactor , "] not found.");
        }
        sensorStarePoint.setLatitude(stareLatitude_deg);
        sensorStarePoint.setLongitude(stareLongitude_deg);
    }
    else
    {
        UXAS_LOG_ERROR("SensorSteering::FindSensorPointingPosition::"," Can not point sensor. waypoint number [" , waypointNumber , "] not found.");
    }
}


void SensorSteeringSegments::AddSegment(std::vector<std::shared_ptr<SensorSteering::PointData> >& waypoints,std::vector<std::shared_ptr<SensorSteering::PointData> >& roadpoints)
{
    auto sensorSteering = std::make_shared<SensorSteering>();
    sensorSteering->Initialize(waypoints,roadpoints);
    if(!waypoints.empty())
    {
        m_idVsSensorSteering[waypoints.front()->m_id] = sensorSteering;
    }
    else
    {
        UXAS_LOG_ERROR("SensorSteeringSegments::AddSegment::"," Waypoint vector was empty.");
    }
}

void SensorSteeringSegments::FindSensorStarePoint(const int64_t& waypointNumber, const afrl::cmasi::Location3D* currentLocation, afrl::cmasi::Location3D& sensorStarePoint,uxas::common::utilities::FlatEarth& flatEarth)
{
    if(!m_idVsSensorSteering.empty())
    {
        // find correct segment
        auto lowerBound = m_idVsSensorSteering.lower_bound(waypointNumber);
        if(lowerBound != m_idVsSensorSteering.end())
        {
            if(lowerBound == m_idVsSensorSteering.begin())
            {
                lowerBound->second->FindSensorStarePoint(waypointNumber,currentLocation,sensorStarePoint,flatEarth);
            }
            else
            {
                auto segment = lowerBound;
                segment--;
                segment->second->FindSensorStarePoint(waypointNumber,currentLocation,sensorStarePoint,flatEarth);
            }
        }
        else
        {
            auto segment = m_idVsSensorSteering.end();
            segment--;
            segment->second->FindSensorStarePoint(waypointNumber,currentLocation,sensorStarePoint,flatEarth);
        }
    }
    else
    {
        UXAS_LOG_ERROR("SensorSteeringSegments::FindSensorStarePoint::"," there are no segments.");
    }
}


}       //namespace utilities
}       //namespace common
}       //namespace uxas

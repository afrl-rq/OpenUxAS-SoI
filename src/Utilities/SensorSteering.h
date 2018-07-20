// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================


/* 
 * File:   SensorSteering.h
 * Author: steve, derek
 *
 * Created on May 21, 2018, 10:06 AM
 */

#ifndef SENSORSTEERING_UTILITIES_H
#define SENSORSTEERING_UTILITIES_H

#include "Position.h"
#include "FlatEarth.h"

#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/Waypoint.h"

#include <map>
#include <vector>

namespace uxas
{
namespace common
{
namespace utilities
{


/*! \class SensorSteering
 *\brief This is a  
 * 
 * 
 * Assumptions:
 *  - sensor points to an AGL location
 *  - linear mapping of waypoint path to road
 *  - waypoint numbers are monitonically increasing
 */

class SensorSteering
{
public:
    SensorSteering(){};
    virtual ~SensorSteering(){};
    
    /** brief Copy construction not permitted */
    SensorSteering(SensorSteering const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(SensorSteering const&) = delete;

public:
    struct PointData
    {
        PointData(const int64_t& id,const afrl::cmasi::Location3D* location3D,uxas::common::utilities::FlatEarth& flatEarth)
        :m_point(std::make_shared<n_FrameworkLib::CPosition>(n_Const::c_Convert::toRadians(location3D->getLatitude()),
                                                            n_Const::c_Convert::toRadians(location3D->getLongitude()),location3D->getAltitude(),flatEarth)),m_id{id}
        {};
        PointData(const int64_t& id,const double& north_m, const double& east_m, const double& altitude_m = 0.0)
        :m_point(std::make_shared<n_FrameworkLib::CPosition>(north_m, east_m, altitude_m)),m_id{id}
        {};
        PointData(const PointData& that)
        :m_point(std::make_shared<n_FrameworkLib::CPosition>(that.m_point->m_north_m,that.m_point->m_east_m,that.m_point->m_altitude_m)),m_id{that.m_id}
        {};
        std::shared_ptr<n_FrameworkLib::CPosition> m_point;
        /*! \brief Distance from the start of the points to this point.  */
        double m_cumulativeDistance_m{0.0};
        int64_t m_id{0};
    };
    
    public:
    void Initialize(std::vector<std::shared_ptr<PointData> >& waypoints,std::vector<std::shared_ptr<PointData> >& roadpoints);
    void FindSensorStarePoint(const int64_t& waypointNumber, const afrl::cmasi::Location3D* currentLocation, afrl::cmasi::Location3D& sensorStarePoint,uxas::common::utilities::FlatEarth& flatEarth);

public:
    
    /*! \brief   */
    std::map<int64_t,std::shared_ptr<PointData> > m_idVsWaypoint;
    /*! \brief   NormFactor is 1000*NormFraction, allows for use of integer. */
    std::map<int64_t,std::shared_ptr<PointData> > m_normFactorVsRoadpoint;
    /*! \brief  total length of the waypoint path */
    double m_waypointsLength_m{0.0};
    /*! \brief  total length of the road */
    double m_roadLength_m{0.0};
};

/*! \class SensorSteeringSegments
 *\brief This is a  
 * 
 *  - the number of the first waypoint in the plan is unique across the plans
 *  - waypoint numbers are monotonically increasing
 */

class SensorSteeringSegments
{
public:
    SensorSteeringSegments(){};
    virtual ~SensorSteeringSegments(){};
    
    /** brief Copy construction not permitted */
    SensorSteeringSegments(SensorSteeringSegments const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(SensorSteeringSegments const&) = delete;

public:
    void AddSegment(std::vector<std::shared_ptr<SensorSteering::PointData> >& waypoints,std::vector<std::shared_ptr<SensorSteering::PointData> >& roadpoints);
    void FindSensorStarePoint(const int64_t& waypointNumber, const afrl::cmasi::Location3D* currentLocation, afrl::cmasi::Location3D& sensorStarePoint,uxas::common::utilities::FlatEarth& flatEarth);

private:
    /*! \brief   */
    std::map<int64_t,std::shared_ptr<SensorSteering> > m_idVsSensorSteering;
};


}       //namespace utilities
}       //namespace common
}       //namespace uxas


#endif /* SENSORSTEERING_UTILITIES_H */


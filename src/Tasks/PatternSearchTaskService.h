// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_PatternSearch.h
 * Author: steve
 *
 * Created on February 16, 2016, 6:17 PM
 */

#ifndef UXAS_SERVICE_TASK_PATTERN_SEARCH_TASK_SERVICE_H
#define UXAS_SERVICE_TASK_PATTERN_SEARCH_TASK_SERVICE_H

#include "Position.h"

#include "TaskServiceBase.h"
#include "UnitConversions.h"
#include "Dpss.h"    //from OHARA
#include "SensorSteering.h"

#include "uxas/messages/task/SensorFootprint.h"
#include "uxas/messages/task/SensorFootprintRequests.h"
#include "uxas/messages/route/RoutePlanRequest.h"
#include "afrl/impact/PatternSearchTask.h"
#include "afrl/impact/AreaSearchPattern.h"

#include <cstdint> // int64_t
#include <unordered_map>

namespace uxas
{
namespace service
{
namespace task
{

/*! \class PatternSearchTaskService
    \brief A component that implements the IMPACT PatternAreaSearchTask message
 * 
 * Options:
 *  - NONE
 * 
 * Subscribed Messages:
 *  - uxas::messages::task::SensorFootprintResponse
 *  - uxas::messages::route::RouteResponse
 * 
 * Sent Messages:
 *  - uxas::messages::task::SensorFootprintRequests
 *  - afrl::cmasi::VehicleActionCommand
 *  - uxas::messages::uxnative::VideoRecord
 *
 * TASK: Subscribed Messages:
 *  - afrl::cmasi::EntityState
 *  - afrl::cmasi::EntityConfiguration
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::vehicles::GroundVehicleState
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - afrl::vehicles::SurfaceVehicleState
 *  - afrl::vehicles::SurfaceVehicleConfiguration
 *  - uxas::messages::task::UniqueAutomationRequest
 *  - uxas::messages::task::UniqueAutomationResponse
 *  - uxas::messages::route::RoutePlanResponse
 *  - uxas::messages::task::TaskImplementationRequest
 * 
 * TASK: Sent Messages:
 *  - uxas::messages::task::TaskInitialized
 *  - uxas::messages::task::TaskActive
 *  - uxas::messages::task::TaskComplete
 *  - uxas::messages::route::RoutePlanRequest
 *  - uxas::messages::task::TaskPlanOptions
 *  - uxas::messages::task::TaskImplementationResponse
 */

//class cc_Task_PatternSearch : public TaskBase

class PatternSearchTaskService : public TaskServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("PatternSearchTaskService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(), "afrl.impact.PatternSearchTask"};
        return (registryServiceTypeNames);
    };

    static const std::string&
    s_directoryName()
    {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create()
    {
        return new PatternSearchTaskService;
    };

    PatternSearchTaskService();

    virtual
    ~PatternSearchTaskService();

private:

    static
    ServiceBase::CreationRegistrar<PatternSearchTaskService> s_registrar;

    /** brief Copy construction not permitted */
    PatternSearchTaskService(PatternSearchTaskService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(PatternSearchTaskService const&) = delete;

    bool configureTask(const pugi::xml_node& serviceXmlNode) override;
    bool processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;
    bool isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse, std::shared_ptr<TaskOptionClass>& taskOptionClass,
                                                          int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route) override;


public:
    const double m_defaultElevationLookAngle_rad = 60.0 * n_Const::c_Convert::dDegreesToRadians(); //60 deg down
public: //virtual
    virtual void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) override;
    virtual void buildTaskPlanOptions() override;

private:
    bool isCalculateOption(const std::vector<int64_t>& eligibleEntities,
                           const double& nominalAltitude_m, const double& nominalSpeed_mps,
                           const double& searchHeading_rad, const double& elevationLookAngle_rad,
                           int64_t& optionId, std::string& algebraString); //NOTE:: optionId can be returned, changed, algebra string is returned
    bool isCalculatePatternScanRoute(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
                                     const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint,
                                     std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest);
    bool isCalculatePatternScanRoute_Spiral(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
                                            const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint);
    bool isCalculatePatternScanRoute_Sector(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
                                            const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint,
                                            std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest);
    bool isCalculatePatternScanRoute_Sweep(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
                                           const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint,
                                           std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest);
    bool isAddDpssSteering(std::shared_ptr<TaskOptionClass>& pTaskOptionClass, std::vector<Dpss_Data_n::xyPoint>& vxyTrueRoadPoints, std::vector<Dpss_Data_n::xyPoint>& vxyWaypoints);
private:

    struct s_SearchLeg
    {

        s_SearchLeg(const n_FrameworkLib::CPosition& startPosition, const n_FrameworkLib::CPosition& endPosition, const double& heading_deg)
        : m_startPosition(startPosition), m_endPosition(endPosition), m_heading_deg(heading_deg) { }
        n_FrameworkLib::CPosition m_startPosition;
        n_FrameworkLib::CPosition m_endPosition;
        double m_heading_deg = {0.0};
    };
private:
    std::shared_ptr<afrl::impact::PatternSearchTask> m_patternSearchTask;
    std::shared_ptr<afrl::impact::PointOfInterest> m_pointOfInterest;
    double m_waypointSpacing_m = {50.0};
    double m_spiralCenterRadius_m{200.0};
    bool m_isUseDpss = {false};
    std::unordered_multimap<int64_t, std::shared_ptr<Dpss> > m_optionIdVsDpss;
    std::shared_ptr<Dpss> m_activeDpss;

    std::unordered_map<int64_t,std::shared_ptr<uxas::common::utilities::SensorSteeringSegments> > m_optionIdVsSensorSteeringSegments;
    std::shared_ptr<uxas::common::utilities::SensorSteeringSegments> m_activeSensorSteeringSegments;
    bool m_isVideoStreamActionSent{false};
    
    /*! \brief  local copy of flatearth to allow storage of north/east coordinates*/
    uxas::common::utilities::FlatEarth m_flatEarth;


public:

private:




};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_PATTERN_SEARCH_TASK_SERVICE_H */


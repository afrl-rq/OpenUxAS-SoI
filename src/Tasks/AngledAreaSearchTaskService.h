// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_AngledAreaSearch.h
 * Author: steve
 *
 * Created on October 19, 2015, 6:17 PM
 */

#ifndef UXAS_SERVICE_TASK_ANGLED_AREA_SEARCH_TASK_SERVICE_H
#define UXAS_SERVICE_TASK_ANGLED_AREA_SEARCH_TASK_SERVICE_H

#include "TaskServiceBase.h"
#include "UnitConversions.h"

#include "uxas/messages/task/SensorFootprintRequests.h"
#include "uxas/messages/route/RouteRequest.h"
#include "afrl/impact/AngledAreaSearchTask.h"

#include <cstdint> // int64_t
#include <unordered_map>

namespace uxas
{
namespace service
{
namespace task
{

/*! \class AngledAreaSearchTaskService
    \brief A component that implements the IMPACT AngledAreaSearchTask message
 * 
 * Options:
 *  - NONE
 * 
 * Subscribed Messages:
 *  - uxas::messages::task::SensorFootprintResponse
 *  - uxas::messages::route::RouteResponse
 * 
 * Sent Messages:
 *  - uxas::messages::route::RoutePlanRequest
 *  - uxas::messages::task::SensorFootprintRequests
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

//class cc_Task_AngledAreaSearch : public TaskBase

class AngledAreaSearchTaskService : public TaskServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("AngledAreaSearchTaskService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(), "afrl.impact.AngledAreaSearchTask"};
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
        return new AngledAreaSearchTaskService;
    };

    AngledAreaSearchTaskService();

    virtual
    ~AngledAreaSearchTaskService();

private:

    static
    ServiceBase::CreationRegistrar<AngledAreaSearchTaskService> s_registrar;

    /** brief Copy construction not permitted */
    AngledAreaSearchTaskService(AngledAreaSearchTaskService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(AngledAreaSearchTaskService const&) = delete;

private:

    bool configureTask(const pugi::xml_node& serviceXmlNode) override;

    bool processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;


public:
    const double m_defaultElevationLookAngle_rad = 60.0 * n_Const::c_Convert::dDegreesToRadians(); //60 deg down

public: //virtual

    virtual void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) override;
    virtual void buildTaskPlanOptions() override;

private:
    bool isCalculateOption(const int64_t& eligibleEntity,
                           const double& nominalAltitude_m, const double& nominalSpeed_mps,
                           const double& searchHeading_rad, const double& elevationLookAngle_rad,
                           int64_t& optionId, std::string & algebraString); //NOTE:: optionId can be returned, changed, algebra string is returned
    bool isCalculateRasterScanRoute(std::shared_ptr<TaskOptionClass>& taskOptionClass, const double& laneSpacing_m,
                                    const double& sensorHorizontalToLeadingEdge_m, const double& sensorHorizontalToTrailingEdge_m,
                                    std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest);


private:

private:
    std::shared_ptr<afrl::impact::AngledAreaSearchTask> m_angledAreaSearchTask;
    std::shared_ptr<afrl::impact::AreaOfInterest> m_areaOfInterest;

    int64_t lane_spacing_min_m = -1;
    int64_t lane_spacing_max_m = -1;

    std::unordered_map<int64_t, std::set<int64_t>> m_entityIDsVsTaskOptions;

public:

private:




};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_ANGLED_AREA_SEARCH_TASK_SERVICE_H */


// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_ImpactPointSearch.h
 * Author: steve
 *
 * Created on February 12, 2015, 6:17 PM
 */

#ifndef UXAS_SERVICE_TASK_IMPACT_POINT_SEARCH_TASK_SERVICE_H
#define UXAS_SERVICE_TASK_IMPACT_POINT_SEARCH_TASK_SERVICE_H

#include "TaskServiceBase.h"
#include "ServiceBase.h"

#include "afrl/cmasi/AutomationRequest.h"
#include "afrl/impact/ImpactPointSearchTask.h"
#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityState.h"
#include "uxas/messages/task/TaskPlanOptions.h"
#include "uxas/messages/task/TaskImplementationRequest.h"
#include "uxas/messages/route/RoutePlan.h"
#include "afrl/cmasi/KeepOutZone.h"
#include <afrl/vehicles/SurfaceVehicleState.h>
#include "visilibity.h"

#include <cstdint> // int64_t
#include <unordered_set>
#include <unordered_map>

namespace uxas
{
namespace service
{
namespace task
{

/*! \class ImpactPointSearchTaskService
    \brief A service that implements the impact point search task.

        //AutomationRequest

        //For each eligible entity, calculate the
        //planning points required to calculate
        //task costs:
        //1) Request sensor footprint information
        //for all eligible vehicles (if required)

            
        // ->SensorFootprintRequest
        //SensorFootprintResponse
        
        //2) Find task options and composition.
        //3) For each option, calculate planning
        //points.

        // ->RouteRequest (cost only)
        //RouteResponse (cost only)

        //4) Send options and composition.
        
        // ->TaskPlanOptions
        //TaskImplementationRequest

        //1) Construct final plans
        //2) Cache assignment for use during
        //execution        
        
        // ->RouteRequest
        //RouteResponse
        // ->TaskImplementationResponse
        //AirVehicleState

        //Tasks monitor VehicleStates to act
        //on assigned portions of the plan,
        //e.g., starts recording video based
        //on vehicle state
 * 
 * Options:
 *  - NONE
 * 
 * Subscribed Messages:
 *  - 
 * 
 * Sent Messages:
 *  - afrl::cmasi::VehicleActionCommand
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

//class cc_Task_ImpactPointSearch : public TaskBase

class ImpactPointSearchTaskService : public TaskServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("ImpactPointSearchTaskService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(), "afrl.impact.ImpactPointSearchTask"};
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
        return new ImpactPointSearchTaskService;
    };

    ImpactPointSearchTaskService();

    virtual
    ~ImpactPointSearchTaskService();

private:

    static
    ServiceBase::CreationRegistrar<ImpactPointSearchTaskService> s_registrar;

    /** brief Copy construction not permitted */
    ImpactPointSearchTaskService(ImpactPointSearchTaskService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(ImpactPointSearchTaskService const&) = delete;

    bool
    configureTask(const pugi::xml_node& serviceXmlNode) override;

public: //virtual
    virtual void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) override;
    virtual void buildTaskPlanOptions() override;
    virtual bool isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse, std::shared_ptr<TaskOptionClass>& taskOptionClass,
                                                          int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route) override;

private:
    bool isCalculateOption(const int64_t& taskId, int64_t& optionId, const double& wedgeHeading_rad);
private:
    std::shared_ptr<afrl::impact::ImpactPointSearchTask> m_pointSearchTask;
    std::shared_ptr<afrl::impact::PointOfInterest> m_pointOfInterest;
    std::unordered_map < int64_t, std::shared_ptr<VisiLibity::Polygon > > m_KeepOutZoneIDVsPolygon;
};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_IMPACT_POINT_SEARCH_TASK_SERVICE_H */


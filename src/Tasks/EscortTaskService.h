// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_EscortTask.h
 * Author: derek
 * 
 * Created on March 7, 2016, 3:03 PM
 */

#ifndef UXAS_SERVICE_TASK_ESCORT_TASK_SERVICE_H
#define UXAS_SERVICE_TASK_ESCORT_TASK_SERVICE_H

#include "TaskServiceBase.h"
#include "ServiceBase.h"

#include "afrl/cmasi/AutomationRequest.h"
#include "afrl/impact/EscortTask.h"
#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityState.h"
#include "uxas/messages/task/TaskPlanOptions.h"
#include "uxas/messages/task/TaskImplementationRequest.h"
#include "uxas/messages/route/RoutePlan.h"

#include <cstdint> // int64_t
#include <unordered_set>
#include <unordered_map>
#include "DynamicTaskServiceBase.h"

namespace uxas
{
namespace service
{
namespace task
{

/*! \class EscortTaskService
    \brief A service that implements a escort task.

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
 *  - afrl::cmasi::MissionCommand
 *  - afrl::cmasi::AutomationResponse
 *  - afrl::cmasi::FollowPathCommand
 *  - afrl::impact::LineOfInterest
 * 
 * Sent Messages:
 *  - afrl::cmasi::MissionCommand
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
 * 
 */

//class cc_Task_EscortTask : public TaskBase

class EscortTaskService : public DynamicTaskServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("EscortTaskService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(), "afrl.impact.EscortTask"};
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
        return new EscortTaskService;
    };

    EscortTaskService();

    virtual
    ~EscortTaskService();

private:

    static
    ServiceBase::CreationRegistrar<EscortTaskService> s_registrar;

    /** brief Copy construction not permitted */
    EscortTaskService(EscortTaskService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(EscortTaskService const&) = delete;

    bool
    configureDynamicTask(const pugi::xml_node& serviceXmlNode) override;

    virtual bool processRecievedLmcpMessageDynamicTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;

    virtual std::shared_ptr<afrl::cmasi::Location3D> calculateTargetLocation(const std::shared_ptr<afrl::cmasi::EntityState> entityState) override;


private:
    void CalculateTargetPoint(std::shared_ptr<afrl::cmasi::Location3D>& targetLocation, double targetHeading, double targetSpeed, std::shared_ptr<afrl::impact::EscortTask>& task);
    double DistanceToLine(std::shared_ptr<afrl::cmasi::Location3D>& loc, std::shared_ptr<afrl::impact::LineOfInterest>& path);
    bool FlipLine(std::shared_ptr<afrl::cmasi::Location3D>& loc, double heading, std::shared_ptr<afrl::impact::LineOfInterest>& path);
private:
    std::shared_ptr<afrl::impact::EscortTask> m_escortTask;
    std::shared_ptr<afrl::cmasi::EntityState> m_supportedEntityStateLast;
};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_ESCORT_TASK_SERVICE_H */


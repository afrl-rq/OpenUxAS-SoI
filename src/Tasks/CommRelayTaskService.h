// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_CommRelayTask.h
 * Author: Derek & steve
 *
 * Created on March 7, 2016, 6:17 PM
 */

#ifndef UXAS_SERVICE_TASK_COMM_RELAY_TASK_SERVICE_H
#define UXAS_SERVICE_TASK_COMM_RELAY_TASK_SERVICE_H

#include "TaskServiceBase.h"
#include "ServiceBase.h"

#include "afrl/cmasi/AutomationRequest.h"
#include "afrl/impact/CommRelayTask.h"
#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/VehicleActionCommand.h"
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

/*! \class c_Task_CommRelayTask
    \brief A component that implements a watchtask.

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
 * Configuration String:
 *  <Service Type="HelloWorld" StringToSend="Hello World!" SendPeriod_ms="1000" />
 * 
 * Options:
 *  - 
 *  - 
 *  - 
 *  - 
 *  - 
 *  - 
 * 
 * Subscribed Messages:
 *  - 
 *  - 
 *  - 
 *  - 
 *  - 
 *  - 
 *  - 
 * 
 * Sent Messages:
 *  - 
 *  - 
 *  - 
 *  - 
 *  - 
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

class CommRelayTaskService : public DynamicTaskServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("CommRelayTaskService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(), "afrl.impact.CommRelayTask"};
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
        return new CommRelayTaskService;
    };

    CommRelayTaskService();

    virtual
    ~CommRelayTaskService();

private:

    static
    ServiceBase::CreationRegistrar<CommRelayTaskService> s_registrar;

    /** brief Copy construction not permitted */
    CommRelayTaskService(CommRelayTaskService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(CommRelayTaskService const&) = delete;

    bool
    configureDynamicTask(const pugi::xml_node& serviceXmlNode) override;
    
    bool
    processRecievedLmcpMessageDynamicTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;

    virtual std::shared_ptr<afrl::cmasi::Location3D> calculateTargetLocation(const std::shared_ptr<afrl::cmasi::EntityState> entityState) override;


private:
    void moveToHalfWayPoint(const std::shared_ptr<afrl::cmasi::Location3D>& supportedEntityStateLocation);
private:
    std::shared_ptr<afrl::impact::CommRelayTask> m_CommRelayTask;
    std::shared_ptr<afrl::cmasi::Location3D> m_supportedEntityStateLast;
public:

};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_COMM_RELAY_TASK_SERVICE_H */


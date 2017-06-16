// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   RendezvousTask.h
 * Author: derek
 *
 * Created on June 14, 2017, 4:14 PM
 */

#ifndef UXAS_RENDEZVOUS_TASK_H
#define UXAS_RENDEZVOUS_TASK_H

#include "TaskServiceBase.h"
#include "uxas/messages/task/TaskImplementationRequest.h"

#include <unordered_map>

namespace uxas
{
namespace service
{
namespace task
{


/*! \class RendezvousTask
 *  \brief This task will synchronize all involved vehicles at a specified
 *         location (or set of locations) at the same time.
 * 
 *         Loiter patterns are used to ensure that when the latest
 *         vehicle arrives, the others will be in the proper positions
 *         and orientations to satisfy the location specification
 *         simultaneously.
 * 
 *         Relies on a series of AND options in the process algebra
 *         relationship to ensure that when all vehicles in the
 *         rendezvous are assigned.
 * 
 * TASK: Subscribed Messages:
 *  - afrl::cmasi::EntityState
 *  - afrl::cmasi::EntityConfiguration
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::impact::GroundVehicleState
 *  - afrl::impact::GroundVehicleConfiguration
 *  - afrl::impact::SurfaceVehicleState
 *  - afrl::impact::SurfaceVehicleConfiguration
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

class RendezvousTask : public TaskServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="uxas.messages.task.RendezvousTask". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("RendezvousTask");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(),"uxas.messages.task.RendezvousTask"};
        return (registryServiceTypeNames);
    };

    /** \brief If this string is not empty, it is used to create a data 
     * directory to be used by the service. The path to this directory is
     * accessed through the ServiceBase variable m_workDirectoryPath. */
    static const std::string&
    s_directoryName() { static std::string s_string(""); return (s_string); };

    static ServiceBase*
    create()
    {
        return new RendezvousTask;
    };

    RendezvousTask();

    virtual
    ~RendezvousTask();

private:

    static
    ServiceBase::CreationRegistrar<RendezvousTask> s_registrar;

    /** brief Copy construction not permitted */
    RendezvousTask(RendezvousTask const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(RendezvousTask const&) = delete;

    bool configureTask(const pugi::xml_node& serviceXmlNode) override;
    
    bool initializeTask() override;
    
    bool startTask() override;
    
    bool terminateTask() override;
    
    bool processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;

    void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) override;

    void buildTaskPlanOptions() override;
    bool isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
                std::shared_ptr<TaskOptionClass>& taskOptionClass,
                int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route) override;

private:
    // storage for the option entries
    
};


}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_RENDEZVOUS_TASK_H */


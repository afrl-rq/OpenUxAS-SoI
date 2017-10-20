// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   AssignmentCoordinatorTaskService.h
 * Author: steve
 *
 * Created on March 30, 2017, 5:55 PM
 */

#ifndef UXAS_ASSIGNMENT_COORDINATOR_TASK_SERVICE_H
#define UXAS_ASSIGNMENT_COORDINATOR_TASK_SERVICE_H

#include "CallbackTimer.h"
#include "TaskServiceBase.h"

#include "uxas/messages/task/AssignmentCoordinatorTask.h"
#include "uxas/messages/task/AssignmentCoordination.h"
#include "uxas/messages/task/CoordinatedAutomationRequest.h"

#include <mutex>

namespace uxas
{
namespace service
{
namespace task
{


/*! \class AssignmentCoordinatorTaskService
    \brief Manages cooperative assignments between vehicles
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

class AssignmentCoordinatorTaskService : public TaskServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="AssignmentCoordinatorTaskService". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("AssignmentCoordinatorTask");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(), "uxas.messages.task.AssignmentCoordinatorTask"};
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
        return new AssignmentCoordinatorTaskService;
    };

    AssignmentCoordinatorTaskService();

    virtual
    ~AssignmentCoordinatorTaskService();

private:

    static
    ServiceBase::CreationRegistrar<AssignmentCoordinatorTaskService> s_registrar;

    /** brief Copy construction not permitted */
    AssignmentCoordinatorTaskService(AssignmentCoordinatorTaskService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(AssignmentCoordinatorTaskService const&) = delete;

    bool configureTask(const pugi::xml_node& serviceXmlNode) override;
    
    bool initializeTask() override;
    
    bool startTask() override;
    
    bool terminateTask() override;
    
    bool processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;

    void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)override { };

    void buildTaskPlanOptions()override { };

private:
    void CheckAssignmentReady(const int64_t& requestId);
    void CallbackSendAutomationRequest(uxas::common::utilities::c_CallbackTimer::enReturnValue retValue);
    void CheckForAssignmentTimeMax();
    
    
private:
    
    /** brief used to lock any functions that access varibles accessed by the timer thread */
    std::mutex m_timerThreadLock;

    uxas::common::utilities::c_CallbackTimer m_sendTaskAutomationRequestTimer;
    
    std::shared_ptr<uxas::messages::task::AssignmentCoordinatorTask> m_assignmentCoordinatorTask;
    struct CoordinationElements
    {
        std::shared_ptr<uxas::messages::task::CoordinatedAutomationRequest> coordinatedAutomationRequest{std::make_shared<uxas::messages::task::CoordinatedAutomationRequest>()};
        std::unordered_map<int64_t,std::shared_ptr<uxas::messages::task::PlanningState> > entityIdVsPlanningState;
    };
    std::unordered_map<int64_t,std::shared_ptr<CoordinationElements> > m_requestIdVsCoordinationElements;
    std::shared_ptr<afrl::cmasi::EntityState> m_lastLocalEntityState;
    /** brief used to start the given assignment, if it wasn't started before, at the max send time */
    std::multimap<int64_t,int64_t> m_maxTimeVsCoordinatedAutomationRequestId;
};


}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_ASSIGNMENT_COORDINATOR_TASK_SERVICE_H */


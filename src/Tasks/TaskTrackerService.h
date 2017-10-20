// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_TaskTracker.h
 * Author: derek
 *
 * Created on Aug 2, 2015, 8:21 AM
 */

#ifndef UXAS_SERVICE_TASK_TASK_TRACKER_SERVICE_H
#define UXAS_SERVICE_TASK_TASK_TRACKER_SERVICE_H

#include "ServiceBase.h"
#include "afrl/cmasi/CMASI.h"
#include "afrl/impact/IMPACT.h"
#include "afrl/vehicles/VEHICLES.h"
#include "uxas/messages/route/ROUTE.h"

#include "visilibity.h"

#include <memory>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <cstdint>

namespace uxas
{
namespace service
{
namespace task
{

/*! \class TaskTrackerService
    \brief Monitors entity waypoints to determine on-task and task completion 
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

class TaskTrackerService : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("TaskTrackerService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
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
        return new TaskTrackerService;
    };

    TaskTrackerService();

    virtual
    ~TaskTrackerService();

private:

    static
    ServiceBase::CreationRegistrar<TaskTrackerService> s_registrar;

    /** brief Copy construction not permitted */
    TaskTrackerService(TaskTrackerService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(TaskTrackerService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    //bool
    //initialize() override;

    //bool
    //start() override;

    //bool
    //terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


    void HandleMissionCommand(std::shared_ptr<afrl::cmasi::MissionCommand>);
    void HandleVehicleState(std::shared_ptr<afrl::cmasi::EntityState>);

    // storage
    std::unordered_set<int64_t> m_tasks;
    std::unordered_map<int64_t, int64_t> m_taskEmit;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_states;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::MissionCommand> > m_missions;

    // monitor state for which task is being worked
    //             vehicle ID,              task IDs
    std::unordered_map<int64_t, std::unordered_set<int64_t> > m_tasksInProgress;
    //             vehicle ID,                    task ID,   wp ID
    std::unordered_map<int64_t, std::unordered_map<int64_t, int64_t> > m_taskWp;
    std::unordered_set<int64_t> isTaskEligible;

    //             vehicle ID,           task ID,  wp ID
    std::unordered_map<int64_t, std::pair<int64_t, int64_t> > m_override;
};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_TASK_TRACKER_SERVICE_H */

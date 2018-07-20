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
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "uxas/messages/task/TaskImplementationRequest.h"
#include "uxas/messages/task/TaskAssignmentSummary.h"
#include "uxas/messages/task/AssignmentCostMatrix.h"

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
 *         Extension patterns are used to ensure that when the latest
 *         vehicle arrives, the others will be in the proper positions
 *         and orientations to satisfy the location specification
 *         simultaneously.
 * 
 *         Relies on a series of AND options in the process algebra
 *         relationship to ensure that all vehicles in the
 *         rendezvous are assigned.
 */

class RendezvousTask : public TaskServiceBase
{
public:
    static const std::string&
    s_typeName()
    {
        static std::string s_string("RendezvousTask");
        return (s_string);
    }

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(),"uxas.messages.task.RendezvousTask"};
        return (registryServiceTypeNames);
    }

    static const std::string&
    s_directoryName() { static std::string s_string(""); return (s_string); }

    static ServiceBase*
    create()
    {
        return new RendezvousTask;
    }

    RendezvousTask();

    virtual
    ~RendezvousTask();

private:

    static
    ServiceBase::CreationRegistrar<RendezvousTask> s_registrar;
    RendezvousTask(RendezvousTask const&) = delete;
    void operator=(RendezvousTask const&) = delete;
    
    bool
    configureTask(const pugi::xml_node& serviceXmlNode) override;
    virtual bool processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;
    void updateStartTimes(std::shared_ptr<uxas::messages::task::TaskImplementationRequest>& implReq);
    void updateStartTimes(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& implResp);
    double ArrivalDistance(const std::shared_ptr<afrl::cmasi::EntityState>& state);
    std::pair<double, double> SpeedClip(const std::shared_ptr<afrl::cmasi::AirVehicleConfiguration>& avconfig, double& nomSpeed);

    void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) override;
    size_t FindWaypointIndex(const std::vector<afrl::cmasi::Waypoint*> wplist, int64_t wpid);
    void buildTaskPlanOptions() override;

    bool isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
                std::shared_ptr<TaskOptionClass>& taskOptionClass,
                int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route) override;
    
    // key: unique automation request ID, value: task assignment summary 
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::task::TaskAssignmentSummary> > m_assignmentSummary;
    
    // key: unique automation request ID, value: assignment cost matrix
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::task::AssignmentCostMatrix> > m_assignmentCostMatrix;
    
    // key: unique automation request ID, value: map
    //                     key: vehicle ID, value: absolute time at task start in ms
    std::unordered_map<int64_t, std::unordered_map<int64_t, int64_t> > m_taskStartTime;
    std::unordered_map<int64_t, std::unordered_map<int64_t, bool> > m_taskEncountered;
    
    // key: vehicle ID, value: pair (time of valuation, remaining distance)
    std::unordered_map<int64_t, std::pair<int64_t, double> > m_distanceRemaining;
};


} //namespace task
} //namespace service
} //namespace uxas

#endif /* UXAS_RENDEZVOUS_TASK_H */


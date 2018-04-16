// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   RendezvousTask.cpp
 * Author: derek
 *
 * Created on June 14, 2017, 4:14 PM
 */

// include header for this service
#include "RendezvousTask.h"
#include "uxas/messages/task/RendezvousTask.h"
#include "uxas/messages/task/TaskOption.h"

// namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{
namespace task
{

// this entry registers the service in the service creation registry
RendezvousTask::ServiceBase::CreationRegistrar<RendezvousTask>
RendezvousTask::s_registrar(RendezvousTask::s_registryServiceTypeNames());

// service constructor
RendezvousTask::RendezvousTask()
: TaskServiceBase(RendezvousTask::s_typeName(), RendezvousTask::s_directoryName()) { }

RendezvousTask::~RendezvousTask()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::~RendezvousTask()");
}

bool
RendezvousTask::configureTask(const pugi::xml_node& ndComponent)
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Configuring Rendezvous Task!" );
    
    // add subscription to TaskAssignmentSummary to determine the complete
    // set of vehicles assigned to this task
    addSubscriptionAddress(uxas::messages::task::TaskImplementationRequest::Subscription);
    
    return true;
}

bool RendezvousTask::initializeTask()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Initializing Rendezvous Task!");
    return true;
}
    
bool RendezvousTask::startTask()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Starting Rendezvous Task!");
    return true;
}
    
bool RendezvousTask::terminateTask()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Terminating Rendezvous Task!");
    return true;
}
    
bool RendezvousTask::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
{
    if(uxas::messages::task::isTaskImplementationRequest(receivedLmcpObject))
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
        auto implReq = std::static_pointer_cast<uxas::messages::task::TaskImplementationRequest>(receivedLmcpObject);
        if(m_task && implReq->getTaskID() == m_task->getTaskID())
        {
            m_implementationRequest[std::make_pair(implReq->getVehicleID(), implReq->getCorrespondingAutomationRequestID())] = implReq;
        }
    }
    else if(uxas::messages::task::isTaskAssignmentSummary(receivedLmcpObject))
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
        auto assignSummary = std::static_pointer_cast<uxas::messages::task::TaskAssignmentSummary>(receivedLmcpObject);
        m_assignmentSummary[assignSummary->getCorrespondingAutomationRequestID()] = assignSummary;
    }
    
    return false;
}

void RendezvousTask::buildTaskPlanOptions()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task building options!");
    
    int64_t taskId(m_task->getTaskID());
    auto rtask = std::static_pointer_cast<uxas::messages::task::RendezvousTask>(m_task);
    
    // add an option for every eligible entity
    for (auto itEligibleEntities = m_speedAltitudeVsEligibleEntityIds.begin();
            itEligibleEntities != m_speedAltitudeVsEligibleEntityIds.end();
            itEligibleEntities++)
    {
        for (auto v : itEligibleEntities->second)
        {
            auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
            auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
            pTaskOptionClass->m_taskOption->setTaskID(taskId);
            pTaskOptionClass->m_taskOption->setOptionID(v);
            pTaskOptionClass->m_taskOption->setCost(0);
            pTaskOptionClass->m_taskOption->setStartLocation(rtask->getLocation()->clone());
            pTaskOptionClass->m_taskOption->setStartHeading(rtask->getHeading());
            pTaskOptionClass->m_taskOption->setEndLocation(rtask->getLocation()->clone());
            pTaskOptionClass->m_taskOption->setEndHeading(rtask->getHeading());
            pTaskOptionClass->m_taskOption->getEligibleEntities().push_back(v);
            m_optionIdVsTaskOptionClass.insert(std::make_pair(v, pTaskOptionClass));
            m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());
        }
    }

    // force all eligible entities to participate in the task
    // TODO: create all subsets of eligible entities of size rtask->getNumberOfParticipants()
    std::string compositionString(".(");
    for (auto itOption : m_taskPlanOptions->getOptions())
    {
        compositionString += "p";
        compositionString += std::to_string(itOption->getOptionID());
        compositionString += " ";
    }
    compositionString += ")";

    m_taskPlanOptions->setComposition(compositionString);

    // send out the options
    sendSharedLmcpObjectBroadcastMessage(m_taskPlanOptions);
    
}

bool RendezvousTask::isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
                std::shared_ptr<TaskOptionClass>& taskOptionClass,
                int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route)
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task processing route response!");
    return true;
}
    
} //namespace task
} //namespace service
} //namespace uxas

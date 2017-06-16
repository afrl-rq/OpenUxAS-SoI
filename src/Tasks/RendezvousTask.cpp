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
: TaskServiceBase(RendezvousTask::s_typeName(), RendezvousTask::s_directoryName()) { };

RendezvousTask::~RendezvousTask()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::~RendezvousTask()");
};

bool
RendezvousTask::configureTask(const pugi::xml_node& ndComponent)
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Configuring Rendezvous Task!" );
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
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
    return false;
}

void RendezvousTask::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling active state!");
}

void RendezvousTask::buildTaskPlanOptions()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task building options!");
    
    int64_t optionId(1);
    int64_t taskId(m_task->getTaskID());
    
    auto rtask = std::static_pointer_cast<uxas::messages::task::RendezvousTask>(m_task);
    if(rtask->getNumberOfParticipants() == rtask->getEligibleEntities().size())
    {
        for(auto v : rtask->getEligibleEntities())
        {
            auto taskOption = new uxas::messages::task::TaskOption;
            taskOption->setTaskID(taskId);
            taskOption->setOptionID(optionId++);
            taskOption->getEligibleEntities().push_back(v);
            taskOption->setStartLocation(rtask->getLocation()->clone());
            taskOption->setStartHeading(rtask->getHeading());
            taskOption->setEndLocation(rtask->getLocation()->clone());
            taskOption->setEndHeading(rtask->getHeading());
            m_taskPlanOptions->getOptions().push_back(taskOption);
            auto topt = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
            m_optionIdVsTaskOptionClass[taskOption->getOptionID()] = std::shared_ptr<TaskOptionClass>(new TaskOptionClass(topt));
        }
    }

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
    
}; //namespace task
}; //namespace service
}; //namespace uxas

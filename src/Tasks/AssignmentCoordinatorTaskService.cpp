// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   AssignmentCoordinatorTaskService.cpp
 * Author: steve
 *
 * Created on March 30, 2017, 5:55 PM
 *
 * <Service Type="AssignmentCoordinatorTaskService"/>
 * 
 */

// include header for this service
#include "AssignmentCoordinatorTaskService.h"

#include "UxAS_Time.h"


#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AirVehicleStateDescendants.h"
#include "uxas/messages/task/TaskAutomationRequest.h"
#include "uxas/messages/task/TaskAutomationResponse.h"

#include <iostream>     // std::cout, cerr, etc

// convenience definitions for the option strings
#define STRING_XML_OPTION_STRING "OptionString"
#define STRING_XML_OPTION_INT "OptionInt"

#define CHECK_TO_SEND_REQUEST_PERIOD_MS (1000)

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>AssignmentCoordinatorTaskService:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();

// namespace definitions
namespace uxas // uxas::
{
namespace service // uxas::service::
{
namespace task // uxas::service::task
{

// this entry registers the service in the service creation registry
AssignmentCoordinatorTaskService::ServiceBase::CreationRegistrar<AssignmentCoordinatorTaskService>
AssignmentCoordinatorTaskService::s_registrar(AssignmentCoordinatorTaskService::s_registryServiceTypeNames());

// service constructor

AssignmentCoordinatorTaskService::AssignmentCoordinatorTaskService()
: TaskServiceBase(AssignmentCoordinatorTaskService::s_typeName(), AssignmentCoordinatorTaskService::s_directoryName())
, m_sendTaskAutomationRequestTimer(uxas::common::utilities::c_CallbackTimer::tmrtypPeriodic) { };

AssignmentCoordinatorTaskService::~AssignmentCoordinatorTaskService()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::~AssignmentCoordinatorTaskService()");
};

bool
AssignmentCoordinatorTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    bool isSuccess(true);

    if (uxas::messages::task::isAssignmentCoordinatorTask(m_task.get()))
    {
        m_assignmentCoordinatorTask = std::static_pointer_cast<uxas::messages::task::AssignmentCoordinatorTask>(m_task);
        if (!m_assignmentCoordinatorTask)
        {
            UXAS_LOG_ERROR(s_typeName(), "::bConfigure failed to cast a AssignmentCoordinatorTaskService from the task pointer.");
            isSuccess = false;
        }
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::bConfigure failed: taskObject[", m_task->getFullLmcpTypeName(), "] is not a AssignmentCoordinatorTaskService.");
        isSuccess = false;
    }

    // subscribe to messages::
    //TODO:: add entities
    //    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    
    // Air Vehicle States
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::AirVehicleStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);
    addSubscriptionAddress(uxas::messages::task::CoordinatedAutomationRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskAutomationResponse::Subscription);
    addSubscriptionAddress(uxas::messages::task::AssignmentCoordination::Subscription);

    return (isSuccess);
}

bool AssignmentCoordinatorTaskService::initializeTask()
{
    // perform any required initialization before the service is started
    //std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;

    return (true);
}

bool AssignmentCoordinatorTaskService::startTask()
{
    // perform any actions required at the time the service starts
    std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with Entity ID [" << m_entityId << "] *** " << std::endl;

    m_sendTaskAutomationRequestTimer.StartCallbackTimer(CHECK_TO_SEND_REQUEST_PERIOD_MS, std::bind(&AssignmentCoordinatorTaskService::CallbackSendAutomationRequest, this, std::placeholders::_1));

    return (true);
};

bool AssignmentCoordinatorTaskService::terminateTask()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    m_sendTaskAutomationRequestTimer.KillTimer();

    return (true);
}

bool AssignmentCoordinatorTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
{
    if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpObject))
    {
        auto airVehicleState = std::static_pointer_cast<afrl::cmasi::AirVehicleState> (receivedLmcpObject);
        if(airVehicleState->getID() == m_entityId)
        {
            m_lastLocalEntityState.reset(airVehicleState->clone());
        }
    }
    else if (uxas::messages::task::isAssignmentCoordination(receivedLmcpObject))
    {
        std::lock_guard<std::mutex> lock(m_timerThreadLock);
        auto assignmentCoordination = std::static_pointer_cast<uxas::messages::task::AssignmentCoordination> (receivedLmcpObject);
        if (m_requestIdVsCoordinationElements.find(assignmentCoordination->getCoordinatedAutomationRequestID()) == m_requestIdVsCoordinationElements.end())
        {
            m_requestIdVsCoordinationElements.insert(std::make_pair(assignmentCoordination->getCoordinatedAutomationRequestID(), std::make_shared<CoordinationElements>()));
        }
        m_requestIdVsCoordinationElements[assignmentCoordination->getCoordinatedAutomationRequestID()]->
                entityIdVsPlanningState[assignmentCoordination->getPlanningState()->getEntityID()] =
                std::shared_ptr<uxas::messages::task::PlanningState>(assignmentCoordination->getPlanningState()->clone());
//        COUT_FILE_LINE_MSG("assignmentCoordination->getCoordinatedAutomationRequestID()[" << assignmentCoordination->getCoordinatedAutomationRequestID() << "]")
        CheckAssignmentReady(assignmentCoordination->getCoordinatedAutomationRequestID());
    }
    else if (uxas::messages::task::isCoordinatedAutomationRequest(receivedLmcpObject))
    {
        std::lock_guard<std::mutex> lock(m_timerThreadLock);
        auto coordinatedAutomationRequest = std::static_pointer_cast<uxas::messages::task::CoordinatedAutomationRequest> (receivedLmcpObject);
        assert(coordinatedAutomationRequest);
        //ASSUME: CoordinatedAutomationRequest messages have unique IDs
        if (m_requestIdVsCoordinationElements.find(coordinatedAutomationRequest->getRequestID()) == m_requestIdVsCoordinationElements.end())
        {
            m_requestIdVsCoordinationElements.insert(std::make_pair(coordinatedAutomationRequest->getRequestID(), std::make_shared<CoordinationElements>()));
        }
        m_requestIdVsCoordinationElements[coordinatedAutomationRequest->getRequestID()]->coordinatedAutomationRequest =
                std::shared_ptr<uxas::messages::task::CoordinatedAutomationRequest>(coordinatedAutomationRequest->clone());

        int64_t maxClockTime_ms = uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms() + coordinatedAutomationRequest->getMaximumResponseTime();
        m_maxTimeVsCoordinatedAutomationRequestId.insert(std::make_pair(maxClockTime_ms, coordinatedAutomationRequest->getRequestID()));

        //ASSUME:: we have already received a local entity state
        if (m_lastLocalEntityState)
        {
            auto localPlanningState = std::make_shared<uxas::messages::task::PlanningState>();
            localPlanningState->setEntityID(m_entityId);
            localPlanningState->setPlanningHeading(m_lastLocalEntityState->getHeading());
            localPlanningState->setPlanningPosition(m_lastLocalEntityState->getLocation()->clone());

            //send coordination
            auto assignmentCoordination = std::make_shared<uxas::messages::task::AssignmentCoordination>();
            assignmentCoordination->setCoordinatedAutomationRequestID(coordinatedAutomationRequest->getRequestID());
            assignmentCoordination->setPlanningState(localPlanningState->clone());
            sendSharedLmcpObjectBroadcastMessage(assignmentCoordination);

            // add planning state to m_requestIdVsCoordinationElements
            m_requestIdVsCoordinationElements[coordinatedAutomationRequest->getRequestID()]->entityIdVsPlanningState.insert(std::make_pair(m_entityId, localPlanningState));
//            COUT_FILE_LINE_MSG("")
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::HAVE NOT RECEIVED AN ENTITY STATE");
        }
        // SET the assignment timer to expire at current time + coordinatedAutomationRequest->getMaximumResponseTime();
//        COUT_FILE_LINE_MSG("")
        CheckAssignmentReady(coordinatedAutomationRequest->getRequestID());
    }
    else if (uxas::messages::task::isTaskAutomationResponse(receivedLmcpObject))
    {
        auto taskAutomationResponse = std::static_pointer_cast<uxas::messages::task::TaskAutomationResponse> (receivedLmcpObject);
        // send out an AutomationResponse (for the waypoint manager)
        auto response = std::shared_ptr<afrl::cmasi::AutomationResponse>(taskAutomationResponse->getOriginalResponse()->clone());
        sendSharedLmcpObjectBroadcastMessage(response);
        
        std::lock_guard<std::mutex> lock(m_timerThreadLock);
        if (m_requestIdVsCoordinationElements.find(taskAutomationResponse->getResponseID()) != m_requestIdVsCoordinationElements.end())
        {
            m_requestIdVsCoordinationElements.erase(taskAutomationResponse->getResponseID());
        }
    }

    return false;
}

void AssignmentCoordinatorTaskService::CheckAssignmentReady(const int64_t& requestId)
{
    auto itCoordinationElements = m_requestIdVsCoordinationElements.find(requestId);
    if (itCoordinationElements == m_requestIdVsCoordinationElements.end())
    {
        UXAS_LOG_ERROR(s_typeName(), "::CheckOnAssignment::isAssignmentReady could not find requestId[", requestId, "]");
    }
    else
    {
        // check for planning state from all of the entities
        bool areEntitiesReady{true};
        // need to chewck to make sure we have a CoordinatedAutomationRequest
        if (requestId == itCoordinationElements->second->coordinatedAutomationRequest->getRequestID())
        {
            for (auto& entityId : itCoordinationElements->second->coordinatedAutomationRequest->getOriginalRequest()->getEntityList())
            {
                if (itCoordinationElements->second->entityIdVsPlanningState.find(entityId) == itCoordinationElements->second->entityIdVsPlanningState.end())
                {
                    areEntitiesReady = false;
                    break;
                }
            }
        }
        else
        {
            areEntitiesReady = false;
        }

        if (areEntitiesReady)
        {
            // send out the taskAutomationRequest
            auto taskAutomationRequest = std::make_shared<uxas::messages::task::TaskAutomationRequest>();
            taskAutomationRequest->setRequestID(requestId);
            taskAutomationRequest->setOriginalRequest(itCoordinationElements->second->coordinatedAutomationRequest->getOriginalRequest()->clone());
            for (auto& itPlanningState : itCoordinationElements->second->entityIdVsPlanningState)
            {
                taskAutomationRequest->getPlanningStates().push_back(itPlanningState.second->clone());
            }
            sendSharedLmcpObjectBroadcastMessage(taskAutomationRequest);
            m_requestIdVsCoordinationElements.erase(requestId);
        }
    }
}

void AssignmentCoordinatorTaskService::CallbackSendAutomationRequest(uxas::common::utilities::c_CallbackTimer::enReturnValue retValue)
{
    switch (retValue)
    {
        default:
        case uxas::common::utilities::c_CallbackTimer::retNormal:
            CheckForAssignmentTimeMax();
            break;
        case uxas::common::utilities::c_CallbackTimer::retCancel:
            break;
    }
}

void AssignmentCoordinatorTaskService::CheckForAssignmentTimeMax()
{
    std::lock_guard<std::mutex> lock(m_timerThreadLock);

    int64_t currentTime_ms{uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms()};

    bool idToErase{false};

    auto itCoordinatedAutomationRequestIdMax = m_maxTimeVsCoordinatedAutomationRequestId.lower_bound(currentTime_ms);
    for (auto itCoordinatedAutomationRequestId = m_maxTimeVsCoordinatedAutomationRequestId.begin();
            itCoordinatedAutomationRequestId != itCoordinatedAutomationRequestIdMax;
            itCoordinatedAutomationRequestId++)
    {
        idToErase = true;
        // find the corresponding CoordinatedAutomationRequest and send a taskautomation request
        auto itCoordinationElements = m_requestIdVsCoordinationElements.find(itCoordinatedAutomationRequestId->second);
        if (itCoordinationElements != m_requestIdVsCoordinationElements.end())
        {
            // send out the taskAutomationRequest
            auto taskAutomationRequest = std::make_shared<uxas::messages::task::TaskAutomationRequest>();
            taskAutomationRequest->setRequestID(itCoordinationElements->first);
            taskAutomationRequest->setOriginalRequest(itCoordinationElements->second->coordinatedAutomationRequest->getOriginalRequest()->clone());
            taskAutomationRequest->getOriginalRequest()->getEntityList().clear();
            for (auto& itPlanningState : itCoordinationElements->second->entityIdVsPlanningState)
            {
                taskAutomationRequest->getOriginalRequest()->getEntityList().push_back(itPlanningState.second->getEntityID());
                taskAutomationRequest->getPlanningStates().push_back(itPlanningState.second->clone());
            }
            sendSharedLmcpObjectBroadcastMessage(taskAutomationRequest);
        }
    }
    if ((idToErase) && (m_maxTimeVsCoordinatedAutomationRequestId.begin() != itCoordinatedAutomationRequestIdMax))
    {
        m_maxTimeVsCoordinatedAutomationRequestId.erase(m_maxTimeVsCoordinatedAutomationRequestId.begin(), itCoordinatedAutomationRequestIdMax);
    }
}


}; //namespace task
}; //namespace service
}; //namespace uxas

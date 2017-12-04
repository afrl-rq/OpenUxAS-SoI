// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   AutomationRequestValidatorService.cpp
 * Author: derek
 * 
 * Created on Aug 24, 2015, 9:31 AM
 */

#include "AutomationRequestValidatorService.h"

#include "TimeUtilities.h"
#include "UxAS_Log.h"
#include "UxAS_TimerManager.h"

#include "uxas/messages/task/TaskInitialized.h"
#include "uxas/messages/task/TaskAutomationRequest.h"
#include "uxas/messages/task/TaskAutomationResponse.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"
#include "afrl/cmasi/AutomationRequest.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/impact/ImpactAutomationRequest.h"
#include "afrl/impact/ImpactAutomationResponse.h"
#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"

#include "afrl/cmasi/ServiceStatus.h"
#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityConfigurationDescendants.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/EntityStateDescendants.h"
#include "afrl/cmasi/RemoveTasks.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"

#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/TaskDescendants.h"    


#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"


#include "pugixml.hpp"

#define STRING_XML_MAX_RESPONSE_TIME_MS "MaxResponseTime_ms"

#define COUT_INFO_MSG(MESSAGE) std::cout << "<>AutomationRequestValidatorService::" << MESSAGE << std::endl;std::cout.flush();

namespace uxas
{
namespace service
{
AutomationRequestValidatorService::ServiceBase::CreationRegistrar<AutomationRequestValidatorService>
AutomationRequestValidatorService::s_registrar(AutomationRequestValidatorService::s_registryServiceTypeNames());

AutomationRequestValidatorService::AutomationRequestValidatorService()
: ServiceBase(AutomationRequestValidatorService::s_typeName(), AutomationRequestValidatorService::s_directoryName())
{
};

AutomationRequestValidatorService::~AutomationRequestValidatorService()
{
    uint64_t delayTime_ms{1000};
    if (m_responseTimerId && !uxas::common::TimerManager::getInstance().destroyTimer(m_responseTimerId, delayTime_ms))
    {
        UXAS_LOG_WARN("AutomationRequestValidatorService::~AutomationRequestValidatorService failed to destroy response timer "
                "(m_responseTimerId) with timer ID ", m_responseTimerId, " within ", delayTime_ms, " millisecond timeout");
    }
};

bool
AutomationRequestValidatorService::initialize()
{

    // create timer
    m_responseTimerId = uxas::common::TimerManager::getInstance().createTimer(
            std::bind(&AutomationRequestValidatorService::OnResponseTimeout, this), "AutomationRequestValidatorService::OnResponseTimeout()");


    return true;
}

bool
AutomationRequestValidatorService::configure(const pugi::xml_node & ndComponent)
{
    if (!ndComponent.attribute(STRING_XML_MAX_RESPONSE_TIME_MS).empty())
    {
        m_maxResponseTime_ms = ndComponent.attribute(STRING_XML_MAX_RESPONSE_TIME_MS).as_uint();
    }

    addSubscriptionAddress(afrl::cmasi::AutomationRequest::Subscription);
    addSubscriptionAddress(afrl::impact::ImpactAutomationRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::UniqueAutomationResponse::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskAutomationRequest::Subscription);

    //ENTITY CONFIGURATIONS
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
    for(auto child : childconfigs)
        addSubscriptionAddress(child);
    
    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);
    
    // TASKS
    addSubscriptionAddress(afrl::cmasi::RemoveTasks::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskInitialized::Subscription);
    // KEEP-IN/OUT/OPERATING
    addSubscriptionAddress(afrl::cmasi::OperatingRegion::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    
    addSubscriptionAddress(afrl::impact::AreaOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::LineOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::PointOfInterest::Subscription);
    
    // Subscribe to Task and all derivatives of Task
    addSubscriptionAddress(afrl::cmasi::Task::Subscription);
    std::vector< std::string > childtasks = afrl::cmasi::TaskDescendants();
    for(auto child : childtasks)
        addSubscriptionAddress(child);

    return true;
}

bool
AutomationRequestValidatorService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    bool isMessageHandled{false};
    auto entityConfig = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
    if ( entityConfig )
    {
        m_availableConfigurationEntityIds.insert(entityConfig->getID());
        isMessageHandled = true;
    }
    else if ( entityState )
    {
        m_availableStateEntityIds.insert(entityState->getID());
        isMessageHandled = true;
    }
    else if (uxas::messages::task::isTaskInitialized(receivedLmcpMessage->m_object.get()))
    {
        auto taskInitialized = std::static_pointer_cast<uxas::messages::task::TaskInitialized>(receivedLmcpMessage->m_object);
        m_availableStartedTaskIds.insert(taskInitialized->getTaskID());
        isMessageHandled = true;
    }
    else if (afrl::impact::isAreaOfInterest(receivedLmcpMessage->m_object.get()))
    {
        auto areaOfInterest = std::static_pointer_cast<afrl::impact::AreaOfInterest>(receivedLmcpMessage->m_object);
        m_availableAreaOfInterestIds.insert(areaOfInterest->getAreaID());
        isMessageHandled = true;
    }
    else if (afrl::impact::isLineOfInterest(receivedLmcpMessage->m_object.get()))
    {
        auto lineOfInterest = std::static_pointer_cast<afrl::impact::LineOfInterest>(receivedLmcpMessage->m_object);
        m_availableLineOfInterestIds.insert(lineOfInterest->getLineID());
        isMessageHandled = true;
    }
    else if (afrl::impact::isPointOfInterest(receivedLmcpMessage->m_object.get()))
    {
        auto pointOfInterest = std::static_pointer_cast<afrl::impact::PointOfInterest>(receivedLmcpMessage->m_object);
        m_availablePointOfInterestIds.insert(pointOfInterest->getPointID());
        isMessageHandled = true;
    }
    else if (afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
    {
        auto keepInZone = std::static_pointer_cast<afrl::cmasi::KeepInZone>(receivedLmcpMessage->m_object);
        m_availableKeepInZoneIds.insert(keepInZone->getZoneID());
        isMessageHandled = true;
    }
    else if (afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
    {
        auto keepOutZone = std::static_pointer_cast<afrl::cmasi::KeepOutZone>(receivedLmcpMessage->m_object);
        m_availableKeepOutZoneIds.insert(keepOutZone->getZoneID());
        isMessageHandled = true;
    }
    else if (afrl::cmasi::isOperatingRegion(receivedLmcpMessage->m_object.get()))
    {
        auto operatingRegion = std::static_pointer_cast<afrl::cmasi::OperatingRegion>(receivedLmcpMessage->m_object);
        m_availableOperatingRegions[operatingRegion->getID()] = operatingRegion;
        isMessageHandled = true;
    }
    else if (afrl::cmasi::isRemoveTasks(receivedLmcpMessage->m_object.get()))
    {
        auto removeTasks = std::static_pointer_cast<afrl::cmasi::RemoveTasks>(receivedLmcpMessage->m_object);
        for (auto& taskId : removeTasks->getTaskList())
        {
            m_availableTasks.erase(taskId);
            m_availableStartedTaskIds.erase(taskId);
        }
        isMessageHandled = true;
    }
    else if (afrl::cmasi::isAutomationRequest(receivedLmcpMessage->m_object) ||
            afrl::impact::isImpactAutomationRequest(receivedLmcpMessage->m_object) ||
            uxas::messages::task::isTaskAutomationRequest(receivedLmcpMessage->m_object))
    {
        auto uniqueAutomationRequest = std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> (new uxas::messages::task::UniqueAutomationRequest);
        uniqueAutomationRequest->setRequestID(getUniqueEntitySendMessageId());

        if (afrl::impact::isImpactAutomationRequest(receivedLmcpMessage->m_object))
        {
            auto sand = std::static_pointer_cast<afrl::impact::ImpactAutomationRequest>(receivedLmcpMessage->m_object);
            uniqueAutomationRequest->setRequestID(sand->getRequestID());
            m_sandboxMap[uniqueAutomationRequest->getRequestID()] = SANDBOX_AUTOMATION_REQUEST;
            uniqueAutomationRequest->setOriginalRequest(sand->getTrialRequest()->clone());
            uniqueAutomationRequest->setSandBoxRequest(true);
            m_playId[uniqueAutomationRequest->getRequestID()] = sand->getPlayID();
            m_solnId[uniqueAutomationRequest->getRequestID()] = sand->getSolutionID();
        }
        else if (uxas::messages::task::isTaskAutomationRequest(receivedLmcpMessage->m_object))
        {
            auto taskAutomationRequest = std::static_pointer_cast<uxas::messages::task::TaskAutomationRequest>(receivedLmcpMessage->m_object);
            uniqueAutomationRequest->setRequestID(taskAutomationRequest->getRequestID());

            uniqueAutomationRequest->setOriginalRequest((afrl::cmasi::AutomationRequest*) taskAutomationRequest->getOriginalRequest()->clone());
            uniqueAutomationRequest->setSandBoxRequest(taskAutomationRequest->getSandBoxRequest());
            for(auto& planningState : taskAutomationRequest->getPlanningStates())
            {
                uniqueAutomationRequest->getPlanningStates().push_back(planningState->clone());
            }
            m_playId[uniqueAutomationRequest->getRequestID()] = taskAutomationRequest->getRequestID();
            m_sandboxMap[uniqueAutomationRequest->getRequestID()] = TASK_AUTOMATION_REQUEST;
        }
        else
        {
            uniqueAutomationRequest->setOriginalRequest((afrl::cmasi::AutomationRequest*) receivedLmcpMessage->m_object->clone());
            m_sandboxMap[uniqueAutomationRequest->getRequestID()] = AUTOMATION_REQUEST;
        }

        m_waitingRequests.push_back(uniqueAutomationRequest);
        isMessageHandled = true;
    }
    else if (uxas::messages::task::isUniqueAutomationResponse(receivedLmcpMessage->m_object.get()))
    {
        auto resp = std::static_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(receivedLmcpMessage->m_object);
        if (m_sandboxMap.find(resp->getResponseID()) != m_sandboxMap.end())
        {
            if (m_sandboxMap[resp->getResponseID()] == TASK_AUTOMATION_REQUEST)
            {
                auto taskResponse = std::make_shared<uxas::messages::task::TaskAutomationResponse>();
                taskResponse->setOriginalResponse(resp->getOriginalResponse()->clone());
                taskResponse->setResponseID(m_playId[resp->getResponseID()]);
                
                // add FinalStates to task responses
                for(auto st : resp->getFinalStates())
                    taskResponse->getFinalStates().push_back(st->clone());
                sendSharedLmcpObjectBroadcastMessage(taskResponse);
            }
            else if (m_sandboxMap[resp->getResponseID()] == AUTOMATION_REQUEST)
            {
                auto cleanResponse = std::shared_ptr<afrl::cmasi::AutomationResponse>(resp->getOriginalResponse()->clone());
                sendSharedLmcpObjectBroadcastMessage(cleanResponse);
            }
            else
            {
                // look up play and solution IDs
                auto sandResponse = std::shared_ptr<afrl::impact::ImpactAutomationResponse> (new afrl::impact::ImpactAutomationResponse);
                sandResponse->setPlayID(m_playId[resp->getResponseID()]);
                sandResponse->setSolutionID(m_solnId[resp->getResponseID()]);
                sandResponse->setTrialResponse(resp->getOriginalResponse()->clone());
				sandResponse->setSandbox(true);
                sendSharedLmcpObjectBroadcastMessage(sandResponse);
            }
            m_sandboxMap.erase(resp->getResponseID());
        }
        m_waitingForResponse.reset();
        OnResponseTimeout();
        isMessageHandled = true;
    }

    if (!isMessageHandled)
    {
        auto baseTask = std::dynamic_pointer_cast<afrl::cmasi::Task>(receivedLmcpMessage->m_object);
        if (baseTask)
        {
            m_availableStartedTaskIds.erase(baseTask->getTaskID());
            m_availableTasks[baseTask->getTaskID()] = baseTask;
        }
        isMessageHandled = true;
    }
    checkToSendNextRequest();
    return false;
}

void AutomationRequestValidatorService::OnResponseTimeout()
{
    if(!m_waitingForResponse)
    {
        m_isAllClear = true;        
    }
    else
    {
        m_waitingForResponse.reset();
        checkToSendNextRequest();
    }
}

void AutomationRequestValidatorService::checkToSendNextRequest()
{
    if(!m_waitingForResponse && !m_waitingRequests.empty())
    {
         auto uniqueAutomationRequest = m_waitingRequests.front();
        m_waitingRequests.pop_front();
        if (isCheckAutomationRequestRequirements(uniqueAutomationRequest))
        {
            m_isAllClear = false;
            m_waitingForResponse = uniqueAutomationRequest;
            sendSharedLmcpObjectBroadcastMessage(uniqueAutomationRequest);
            
            auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
            serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
            auto keyValuePair = new afrl::cmasi::KeyValuePair;
            std::string message = "UniqueAutomationRequest[" + std::to_string(uniqueAutomationRequest->getRequestID()) + "] - sent";
            keyValuePair->setKey(message);
            serviceStatus->getInfo().push_back(keyValuePair);
            keyValuePair = nullptr;
            sendSharedLmcpObjectBroadcastMessage(serviceStatus);
            // reset the timer
        }
        else //if (isCheckAutomationRequestRequirements(uniqueAutomationRequest))
        {
            if (m_waitingRequests.empty())
            {
                m_waitingRequests.push_back(uniqueAutomationRequest);
            }
            else
            {
                // automation request ID not sent
                std::stringstream reasonForFailure;
                reasonForFailure << "- automation request ID[" << uniqueAutomationRequest->getRequestID() << "] was not ready in time and was not sent." << std::endl;
                UXAS_LOG_WARN(reasonForFailure.str());
                COUT_INFO_MSG(reasonForFailure.str());
                auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
                serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
                auto keyValuePair = new afrl::cmasi::KeyValuePair;
                keyValuePair->setKey(std::string("RequestValidator"));
                keyValuePair->setValue(reasonForFailure.str());
                serviceStatus->getInfo().push_back(keyValuePair);
                keyValuePair = nullptr;
                sendSharedLmcpObjectBroadcastMessage(serviceStatus);
            }
        }
    }
}

bool AutomationRequestValidatorService::isCheckAutomationRequestRequirements(const std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>& uniqueAutomationRequest)
{
    bool isReady{true};
    std::stringstream reasonForFailure;
    reasonForFailure << "Automation Request ID[" << uniqueAutomationRequest->getRequestID() << "] Not Ready ::" << std::endl;

    if (!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())
    {
        // check for required entity configurations, if none are required, make sure there is at least one
        if (!m_availableConfigurationEntityIds.empty())
        {
            if (!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())
            {
                for (auto& id : uniqueAutomationRequest->getOriginalRequest()->getEntityList())
                {
                    //COUT_INFO_MSG("id[" << id << "]")
                    if (m_availableConfigurationEntityIds.find(id) == m_availableConfigurationEntityIds.end())
                    {
                        reasonForFailure << "- EntityConfiguration for Entity Id[" << id << "] not available." << std::endl;
                        isReady = false;
                    }
                }
            }
        }
        else
        {
            reasonForFailure << "- No EntityConfigurations available." << std::endl;
            isReady = false;
        }

        // check for required entity states, if none are required, make sure there is at least one with matching configuration
        if (!m_availableStateEntityIds.empty())
        {
            for (auto& id : uniqueAutomationRequest->getOriginalRequest()->getEntityList())
            {
                bool isReadyLocal{false};
                if (m_availableStateEntityIds.find(id) != m_availableStateEntityIds.end())
                {
                    isReadyLocal = true;
                }
                if(!isReadyLocal)
                {
                    for(auto& planningState: uniqueAutomationRequest->getPlanningStates())
                    {
                        if(planningState->getEntityID() == id)
                        {
                            isReadyLocal = true;
                            break;
                        }
                    }
                }
                if(!isReadyLocal)
                {
                    isReady = false;
                    reasonForFailure << "- EntityState for Entity Id[" << id << "] not available." << std::endl;
                }
            }
        }
        else
        {
            reasonForFailure << "- No EntityStates available." << std::endl;
            isReady = false;
        }
    }
    else //if(!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())
    {
        if (!m_availableConfigurationEntityIds.empty() && !m_availableStateEntityIds.empty())
        {
            bool isFoundAMatch{false};
            for (auto& id1 : m_availableConfigurationEntityIds)
            {
                for (auto& id2 : m_availableConfigurationEntityIds)
                {
                    if (id1 == id2)
                    {
                        isFoundAMatch = true;
                        break;
                    }
                }
                if (isFoundAMatch)
                {
                    break;
                }
            }
            if (!isFoundAMatch)
            {
                reasonForFailure << "- No EntityStates that match EntityConfigurations are available." << std::endl;
                isReady = false;
            }
        }
        else
        {
            if (m_availableConfigurationEntityIds.empty())
            {
                reasonForFailure << "- No EntityConfigurations available." << std::endl;
            }
            else
            {
                reasonForFailure << "- No EntityStates available." << std::endl;
            }
            isReady = false;
        }

    } //if(!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())

    // check for required operating region and keepin/keepout zones
    if (uniqueAutomationRequest->getOriginalRequest()->getOperatingRegion() != 0)
    {
        auto itOperatingRegion = m_availableOperatingRegions.find(uniqueAutomationRequest->getOriginalRequest()->getOperatingRegion());
        if (itOperatingRegion != m_availableOperatingRegions.end())
        {
            for (auto & keepInArea : itOperatingRegion->second->getKeepInAreas())
            {
                if (m_availableKeepInZoneIds.find(keepInArea) == m_availableKeepInZoneIds.end())
                {
                    reasonForFailure << "- KeepInArea Id[" << keepInArea << "] not available." << std::endl;
                    isReady = false;
                }
            }
            for (auto & keepOutArea : itOperatingRegion->second->getKeepOutAreas())
            {
                if (m_availableKeepOutZoneIds.find(keepOutArea) == m_availableKeepOutZoneIds.end())
                {
                    reasonForFailure << "- KeepOutArea Id[" << keepOutArea << "] not available." << std::endl;
                    isReady = false;
                }
            }
        }
        else
        {
            reasonForFailure << "- OperatingRegion Id[" << uniqueAutomationRequest->getOriginalRequest()->getOperatingRegion() << "] not available." << std::endl;
            isReady = false;
        }
    }

    // check for required tasks and task requirements
    for (auto& taskId : uniqueAutomationRequest->getOriginalRequest()->getTaskList())
    {
        auto itTask = m_availableTasks.find(taskId);
        if (itTask != m_availableTasks.end())
        {
            auto itStartedTaskId = m_availableStartedTaskIds.find(taskId);
            if (itStartedTaskId != m_availableStartedTaskIds.end())
            {
                // check for specific task requirements
                if (itTask->second->getFullLmcpTypeName() == afrl::impact::AngledAreaSearchTask::Subscription)
                {
                    auto angledAreaSearchTask = std::static_pointer_cast<afrl::impact::AngledAreaSearchTask>(itTask->second);
                    if (angledAreaSearchTask->getSearchAreaID() != 0)
                    {
                        if (m_availableAreaOfInterestIds.find(angledAreaSearchTask->getSearchAreaID()) == m_availableAreaOfInterestIds.end())
                        {
                            reasonForFailure << "- AreaOfInterest Id[" << angledAreaSearchTask->getSearchAreaID() << "] not available." << std::endl;
                            isReady = false;
                        }
                    }
                }
                else if (itTask->second->getFullLmcpTypeName() == afrl::impact::ImpactLineSearchTask::Subscription)
                {
                    auto impactLineSearchTask = std::static_pointer_cast<afrl::impact::ImpactLineSearchTask>(itTask->second);
                    if (impactLineSearchTask->getLineID() != 0)
                    {
                        if (m_availableLineOfInterestIds.find(impactLineSearchTask->getLineID()) == m_availableLineOfInterestIds.end())
                        {
                            reasonForFailure << "- LineOfInterest Id[" << impactLineSearchTask->getLineID() << "] not available." << std::endl;
                            isReady = false;
                        }
                    }
                }
                else if (itTask->second->getFullLmcpTypeName() == afrl::impact::ImpactPointSearchTask::Subscription)
                {
                    auto impactPointSearchTask = std::static_pointer_cast<afrl::impact::ImpactPointSearchTask>(itTask->second);
                    if (impactPointSearchTask->getSearchLocationID() != 0)
                    {
                        if (m_availablePointOfInterestIds.find(impactPointSearchTask->getSearchLocationID()) == m_availablePointOfInterestIds.end())
                        {
                            reasonForFailure << "- LineOfInterest Id[" << impactPointSearchTask->getSearchLocationID() << "] not available." << std::endl;
                            isReady = false;
                        }
                    }
                }
            }
            else
            {
                reasonForFailure << "- Task with the Id[" << taskId << "] not yet started." << std::endl;
                isReady = false;
            }
        }
        else
        {
            reasonForFailure << "- Task with the Id[" << taskId << "] not available." << std::endl;
            isReady = false;
        }
    }

    if (!isReady)
    {
        UXAS_LOG_WARN(reasonForFailure.str());
        COUT_INFO_MSG(reasonForFailure.str());
        auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
        serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
        auto keyValuePair = new afrl::cmasi::KeyValuePair;
        keyValuePair->setKey(std::string("RequestValidator"));
        keyValuePair->setValue(reasonForFailure.str());
        serviceStatus->getInfo().push_back(keyValuePair);
        keyValuePair = nullptr;
        sendSharedLmcpObjectBroadcastMessage(serviceStatus);
    }

    return (isReady);
}



}; //namespace service
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_PlanBuilder.cpp
 * Author: steve
 * 
 * Created on September 2, 2015, 6:17 PM
 */


#include "PlanBuilderService.h"

#include "UnitConversions.h"
#include "Constants/Convert.h"

#include "uxas/messages/task/UniqueAutomationResponse.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/impact/GroundVehicleState.h"
#include "afrl/impact/SurfaceVehicleState.h"
#include "afrl/cmasi/ServiceStatus.h"



#include "pugixml.hpp"

#include <sstream>
#include <iostream>     // std::cout, cerr, etc

#define STRING_COMPONENT_NAME "PlanBuilder"

#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"

#define STRING_XML_ASSIGNMENT_START_POINT_LEAD_M "AssignmentStartPointLead_m"

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "PLNB-PLNB-PLNB-PLNB:: PlanBuilder:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "PLNB-PLNB-PLNB-PLNB:: PlanBuilder:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();

namespace uxas
{
namespace service
{


PlanBuilderService::ServiceBase::CreationRegistrar<PlanBuilderService>
PlanBuilderService::s_registrar(PlanBuilderService::s_registryServiceTypeNames());

PlanBuilderService::PlanBuilderService()
: ServiceBase(PlanBuilderService::s_typeName(), PlanBuilderService::s_directoryName()) { };

PlanBuilderService::~PlanBuilderService() { };

bool
PlanBuilderService::configure(const pugi::xml_node& ndComponent)

{
    bool isSuccess(true);
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();

    if (!ndComponent.attribute(STRING_XML_ASSIGNMENT_START_POINT_LEAD_M).empty())
    {
        m_assignmentStartPointLead_m = ndComponent.attribute(STRING_XML_ASSIGNMENT_START_POINT_LEAD_M).as_double();
    }


    addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskAssignmentSummary::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskImplementationResponse::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(afrl::impact::GroundVehicleState::Subscription);
    addSubscriptionAddress(afrl::impact::SurfaceVehicleState::Subscription);
    return (isSuccess);
}

bool
PlanBuilderService::initialize()
{
    return (true);
}

bool
PlanBuilderService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    if (receivedLmcpMessage->m_object->getFullLmcpTypeName() == uxas::messages::task::TaskAssignmentSummary::Subscription)
    {
        processTaskAssignmentSummary(std::static_pointer_cast<uxas::messages::task::TaskAssignmentSummary>(receivedLmcpMessage->m_object));
    }
    else if (receivedLmcpMessage->m_object->getFullLmcpTypeName() == uxas::messages::task::TaskImplementationResponse::Subscription)
    {
        processTaskImplementationResponse(std::static_pointer_cast<uxas::messages::task::TaskImplementationResponse>(receivedLmcpMessage->m_object));
    }
    else if (receivedLmcpMessage->m_object->getFullLmcpTypeName() == afrl::cmasi::AirVehicleState::Subscription)
    {
        auto entityState = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        m_entityIdVsEntityState[entityState->getID()] = entityState;
    }
    else if (receivedLmcpMessage->m_object->getFullLmcpTypeName() == afrl::impact::GroundVehicleState::Subscription)
    {
        auto entityState = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        m_entityIdVsEntityState[entityState->getID()] = entityState;
    }
    else if (receivedLmcpMessage->m_object->getFullLmcpTypeName() == afrl::impact::SurfaceVehicleState::Subscription)
    {
        auto entityState = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        m_entityIdVsEntityState[entityState->getID()] = entityState;
    }
    else if (uxas::messages::task::isUniqueAutomationRequest(receivedLmcpMessage->m_object.get()))
    {
        //TODO:: put responses in a map by id
        auto uniqueAutomationRequest = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage->m_object);
        m_uniqueAutomationRequest = uniqueAutomationRequest;
    }
    else
    {
        //        UXAS_LOG_WARN("WARNING::PlanBuilderService::ProcessMessage: MessageType [" 
        //                , receivedLmcpMessage->m_object->getFullLmcpTypeName() 
        //                , "] serviceId[" , m_serviceId
        //                , "] SourceEntityId[" , receivedLmcpMessage->m_attributes->getSourceEntityId()
        //                , "] SourceServiceId[" , receivedLmcpMessage->m_attributes->getSourceServiceId() 
        //                , "] not processed.");
    }
    return (false); // always false implies never terminating service from here
};

void PlanBuilderService::processTaskAssignmentSummary(const std::shared_ptr<uxas::messages::task::TaskAssignmentSummary>& taskAssignmentSummary)
{
    uxas::common::utilities::CUnitConversions unitConversions;
    // reset for new set of plans
    m_taskImplementationId = 0;
    m_entityIdVsTaskImplementationRequests.clear();
    m_entityIdVsTaskImplementationResponses.clear();

    for (auto itTask = taskAssignmentSummary->getTaskList().begin(); itTask != taskAssignmentSummary->getTaskList().end(); itTask++)
    {
        auto taskImplementationRequest = std::make_shared<uxas::messages::task::TaskImplementationRequest>();
        taskImplementationRequest->setRequestID(getNextImplementationId());
        taskImplementationRequest->setStartingWaypointID(getStartingWaypointId()); // this must be after "getNextImplementationId"
        taskImplementationRequest->setVehicleID((*itTask)->getAssignedVehicle());
        taskImplementationRequest->setTaskID((*itTask)->getTaskID());
        taskImplementationRequest->setOptionID((*itTask)->getOptionID());
        taskImplementationRequest->setRegionID(taskAssignmentSummary->getOperatingRegion());
        taskImplementationRequest->setTimeThreshold((*itTask)->getTimeThreshold());

        bool isNewEntity{false};
        if (m_entityIdVsTaskImplementationRequests.find((*itTask)->getAssignedVehicle()) == m_entityIdVsTaskImplementationRequests.end())
        {
            isNewEntity = true;
            m_entityIdVsTaskImplementationRequests[(*itTask)->getAssignedVehicle()] = std::make_shared<std::deque<std::shared_ptr<uxas::messages::task::TaskImplementationRequest> > >();
        }
        if (isNewEntity)
        {

            int64_t startTime_ms{uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms()};
            auto entityState = m_entityIdVsEntityState.find((*itTask)->getAssignedVehicle());
            bool isFoundEntityState{false};

            float startHeading_deg{0.0};
            auto startLocation = std::make_shared<afrl::cmasi::Location3D>();
            for (auto& planningState : m_uniqueAutomationRequest->getPlanningStates())
            {
                if (planningState->getEntityID() == (*itTask)->getAssignedVehicle())
                {
                    startLocation.reset(planningState->getPlanningPosition()->clone());
                    startHeading_deg = planningState->getPlanningHeading();
                    isFoundEntityState = true;
                    break;
                }
            }
            if (!isFoundEntityState)
            {
                if (entityState != m_entityIdVsEntityState.end())
                {
                    isFoundEntityState = true;
                    startLocation.reset(entityState->second->getLocation()->clone());
                    startHeading_deg = entityState->second->getHeading();
                    startTime_ms = entityState->second->getTime();
                }
            }
            if (isFoundEntityState)
            {
                taskImplementationRequest->setStartHeading(startHeading_deg);
                taskImplementationRequest->setStartPosition(startLocation->clone());
                taskImplementationRequest->setStartTime(startTime_ms);

                // add in the assignment start point lead distance
                double north_m(0.0);
                double east_m(0.0);
                unitConversions.ConvertLatLong_degToNorthEast_m(startLocation->getLatitude(),
                                                                startLocation->getLongitude(),
                                                                north_m, east_m);

                north_m += m_assignmentStartPointLead_m * cos(startHeading_deg * n_Const::c_Convert::dDegreesToRadians());
                east_m += m_assignmentStartPointLead_m * sin(startHeading_deg * n_Const::c_Convert::dDegreesToRadians());

                double latitude_deg(0.0);
                double longitude_deg(0.0);
                unitConversions.ConvertNorthEast_mToLatLong_deg(north_m, east_m, latitude_deg, longitude_deg);

                taskImplementationRequest->getStartPosition()->setLatitude(latitude_deg);
                taskImplementationRequest->getStartPosition()->setLongitude(longitude_deg);
            }
            else
            {
                CERR_FILE_LINE_MSG("ERROR::processTaskAssignmentSummary: Entity State for Entity Id[" << (*itTask)->getAssignedVehicle() << "] not found!")

                auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
                serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Error);
                auto keyValuePair = new afrl::cmasi::KeyValuePair;
                keyValuePair->setKey(std::string("No UniqueAutomationResponse"));
                std::string message = "ERROR::processTaskAssignmentSummary: Entity State for Entity Id[" + std::to_string((*itTask)->getAssignedVehicle()) + "] not found!";
                keyValuePair->setValue(message);
                serviceStatus->getInfo().push_back(keyValuePair);
                keyValuePair = nullptr;
                sendSharedLmcpObjectBroadcastMessage(serviceStatus);
            }

        }
        m_entityIdVsTaskImplementationRequests[(*itTask)->getAssignedVehicle()]->push_back(taskImplementationRequest);
    } //for(auto itTask=taskAssignmentSummary->getTaskList().begin();itTask!=taskAssignmen

    // send out the initial requests
    for (auto taskImplementationRequest = m_entityIdVsTaskImplementationRequests.begin();
            taskImplementationRequest != m_entityIdVsTaskImplementationRequests.end();
            taskImplementationRequest++)
    {
        if (!taskImplementationRequest->second->empty())
        {
            auto newRequest = std::static_pointer_cast<avtas::lmcp::Object>(taskImplementationRequest->second->front());
            sendSharedLmcpObjectBroadcastMessage(newRequest);
        }
    }

};

void PlanBuilderService::processTaskImplementationResponse(const std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse)
{
    auto taskImplementationRequest = m_entityIdVsTaskImplementationRequests.find(taskImplementationResponse->getVehicleID());
    if (taskImplementationRequest != m_entityIdVsTaskImplementationRequests.end())
    {
        if ((!taskImplementationRequest->second->empty()) &&
                (taskImplementationRequest->second->front()->getRequestID() == taskImplementationResponse->getResponseID()))
        {
            if (m_entityIdVsTaskImplementationResponses.find(taskImplementationResponse->getVehicleID()) == m_entityIdVsTaskImplementationResponses.end())
            {
                m_entityIdVsTaskImplementationResponses[taskImplementationResponse->getVehicleID()] = std::make_shared<std::deque<std::shared_ptr<uxas::messages::task::TaskImplementationResponse> > >();
            }
            m_entityIdVsTaskImplementationResponses[taskImplementationResponse->getVehicleID()]->push_back(taskImplementationResponse);

            taskImplementationRequest->second->pop_front();
            if (!taskImplementationRequest->second->empty())
            {
                // send next request
                auto newRequest = taskImplementationRequest->second->front();
                newRequest->setStartHeading(taskImplementationResponse->getFinalHeading());
                newRequest->setStartPosition(taskImplementationResponse->getFinalLocation()->clone());
                newRequest->setStartTime(taskImplementationResponse->getFinalTime());
                auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(newRequest);
                sendSharedLmcpObjectBroadcastMessage(newMessage);
            }
            else
            {
                bool isPlanComplete{true};
                for (auto taskImplementationRequests = m_entityIdVsTaskImplementationRequests.begin();
                        taskImplementationRequests != m_entityIdVsTaskImplementationRequests.end();
                        taskImplementationRequests++)
                {
                    if (!taskImplementationRequests->second->empty())
                    {
                        isPlanComplete = false;
                        break;
                    }
                }
                if (isPlanComplete)
                {
                    buildAndSendThePlan();
                }
            }
        }
        else
        {
            CERR_FILE_LINE_MSG("ERROR::processTaskImplementationResponse: TaskImplementationId[" << taskImplementationResponse->getResponseID() << "] was not found for Entity Id[" << taskImplementationResponse->getVehicleID() << "]!")
                    auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
            serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Error);
            auto keyValuePair = new afrl::cmasi::KeyValuePair;
            keyValuePair->setKey(std::string("No UniqueAutomationResponse"));
            std::string message = "ERROR::processTaskImplementationResponse: TaskImplementationId[" + std::to_string(taskImplementationResponse->getResponseID()) + "] was not found for Entity Id[" + std::to_string(taskImplementationResponse->getVehicleID()) + "]!";
            keyValuePair->setValue(message);
            serviceStatus->getInfo().push_back(keyValuePair);
            keyValuePair = nullptr;
            sendSharedLmcpObjectBroadcastMessage(serviceStatus);
        }
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::processTaskImplementationResponse: A TaskImplementationRequest was not found for Entity Id[" << taskImplementationResponse->getVehicleID() << "]!")
                auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
        serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Error);
        auto keyValuePair = new afrl::cmasi::KeyValuePair;
        keyValuePair->setKey(std::string("No UniqueAutomationResponse"));
        std::string message = "ERROR::processTaskAssignmentSummary: A TaskImplementationRequest was not found for Entity Id[" + std::to_string(taskImplementationResponse->getVehicleID()) + "]!";
        keyValuePair->setValue(message);
        serviceStatus->getInfo().push_back(keyValuePair);
        keyValuePair = nullptr;
        sendSharedLmcpObjectBroadcastMessage(serviceStatus);
    }
};

void PlanBuilderService::buildAndSendThePlan()
{
    if (m_uniqueAutomationRequest)
    {
        auto uniqueAutomationResponse = std::make_shared<uxas::messages::task::UniqueAutomationResponse>();
        uniqueAutomationResponse->setResponseID(m_uniqueAutomationRequest->getRequestID());
        for (auto taskImplementationResponses = m_entityIdVsTaskImplementationResponses.begin();
                taskImplementationResponses != m_entityIdVsTaskImplementationResponses.end();
                taskImplementationResponses++)
        {
            if (!taskImplementationResponses->second->empty())
            {
                auto missionCommand = new afrl::cmasi::MissionCommand;
                afrl::cmasi::Waypoint * lastWaypoint(nullptr); // store pointer to last waypoint do not delete, we do not own this pointer
                for (auto taskImplementationResponse = taskImplementationResponses->second->begin();
                        taskImplementationResponse != taskImplementationResponses->second->end();
                        taskImplementationResponse++)
                {
                    for (auto taskWaypoint = (*taskImplementationResponse)->getTaskWaypoints().begin();
                            taskWaypoint != (*taskImplementationResponse)->getTaskWaypoints().end();
                            taskWaypoint++)
                    {
                        if (lastWaypoint != nullptr)
                        {
                            lastWaypoint->setNextWaypoint((*taskWaypoint)->getNumber());
                        }
                        lastWaypoint = (*taskWaypoint)->clone();
                        missionCommand->getWaypointList().push_back(lastWaypoint);
                    }

                }
                lastWaypoint = nullptr; // we do not own this
                missionCommand->setVehicleID((*taskImplementationResponses).first);
                missionCommand->setCommandID(getNextCommandId());
                if (!missionCommand->getWaypointList().empty()) //sanity check
                {
                    missionCommand->setFirstWaypoint(missionCommand->getWaypointList().front()->getNumber());
                }
                uniqueAutomationResponse->getOriginalResponse()->getMissionCommandList().push_back(missionCommand);
                missionCommand = nullptr;
            }
        }
        sendSharedLmcpObjectBroadcastMessage(uniqueAutomationResponse);

        auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
        serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
        auto keyValuePair = new afrl::cmasi::KeyValuePair;
        std::string message = "UniqueAutomationResponse[" + std::to_string(uniqueAutomationResponse->getResponseID()) + "] - sent";
        keyValuePair->setKey(message);
        serviceStatus->getInfo().push_back(keyValuePair);
        keyValuePair = nullptr;
        sendSharedLmcpObjectBroadcastMessage(serviceStatus);
    }
    else
    {
        auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
        serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Error);
        auto keyValuePair = new afrl::cmasi::KeyValuePair;
        keyValuePair->setKey(std::string("No UniqueAutomationResponse"));
        keyValuePair->setValue(std::string("PlanBuilderService::buildAndSendThePlan(): no saved UniqueAutomationRequest!!"));
        serviceStatus->getInfo().push_back(keyValuePair);
        keyValuePair = nullptr;
        sendSharedLmcpObjectBroadcastMessage(serviceStatus);
        UXAS_LOG_ERROR("PlanBuilderService::buildAndSendThePlan(): no saved UniqueAutomationRequest!!");
    }
};







}; //namespace service
}; //namespace uxas

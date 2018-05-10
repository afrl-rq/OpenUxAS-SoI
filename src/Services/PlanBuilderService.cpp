// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
 * File:   PlanBuilderService.cpp
 * Author: steve
 *
 * Created on September 2, 2015, 6:17 PM
 */


#include "PlanBuilderService.h"

#include "UnitConversions.h"
#include "Constants/Convert.h"

#include "uxas/messages/task/UniqueAutomationResponse.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/EntityStateDescendants.h"
#include "afrl/cmasi/ServiceStatus.h"
#include "pugixml.hpp"

//Added
#include "afrl/cmasi/LoiterAction.h"
#include "afrl/cmasi/Waypoint.h"

#include <sstream>
#include <iostream>     // //std::cout, cerr, etc

#define STRING_XML_ASSIGNMENT_START_POINT_LEAD_M "AssignmentStartPointLead_m"

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
    if (!ndComponent.attribute(STRING_XML_ASSIGNMENT_START_POINT_LEAD_M).empty())
    {
        m_assignmentStartPointLead_m = ndComponent.attribute(STRING_XML_ASSIGNMENT_START_POINT_LEAD_M).as_double();
    }

    addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskAssignmentSummary::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskImplementationResponse::Subscription);

    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);
    return true;
}

bool
PlanBuilderService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
    if(entityState)
    {
        m_currentEntityStates[entityState->getID()] = entityState;
    }
    else if(uxas::messages::task::isTaskAssignmentSummary(receivedLmcpMessage->m_object))
    {
        processTaskAssignmentSummary(std::static_pointer_cast<uxas::messages::task::TaskAssignmentSummary>(receivedLmcpMessage->m_object));
    }
    else if(uxas::messages::task::isTaskImplementationResponse(receivedLmcpMessage->m_object))
    {
        processTaskImplementationResponse(std::static_pointer_cast<uxas::messages::task::TaskImplementationResponse>(receivedLmcpMessage->m_object));
    }
    else if(uxas::messages::task::isUniqueAutomationRequest(receivedLmcpMessage->m_object))
    {
        auto uniqueAutomationRequest = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage->m_object);
        m_uniqueAutomationRequests[uniqueAutomationRequest->getRequestID()] = uniqueAutomationRequest;

        // re-initialize state maps (possibly halt completion of over-ridden automation request)
        m_assignmentSummaries[uniqueAutomationRequest->getRequestID()] = std::shared_ptr<uxas::messages::task::TaskAssignmentSummary>(nullptr);
        m_projectedEntityStates[uniqueAutomationRequest->getRequestID()] = std::vector< std::shared_ptr<ProjectedState> >();
        m_remainingAssignments[uniqueAutomationRequest->getRequestID()] = std::deque< std::shared_ptr<uxas::messages::task::TaskAssignment> >();
        m_inProgressResponse[uniqueAutomationRequest->getRequestID()] = std::shared_ptr<uxas::messages::task::UniqueAutomationResponse>(nullptr);
    }

    return (false); // always false implies never terminating service from here
};

void PlanBuilderService::sendError(std::string& errMsg)
{
    auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
    serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Error);
    auto keyValuePair = new afrl::cmasi::KeyValuePair;
    keyValuePair->setKey(std::string("No UniqueAutomationResponse"));
    keyValuePair->setValue(errMsg);
    serviceStatus->getInfo().push_back(keyValuePair);
    sendSharedLmcpObjectBroadcastMessage(serviceStatus);
}

void PlanBuilderService::processTaskAssignmentSummary(const std::shared_ptr<uxas::messages::task::TaskAssignmentSummary>& taskAssignmentSummary)
{
    // validate that this summary corresponds to an existing unique automation request
    auto correspondingAutomationRequest = std::make_shared<uxas::messages::task::UniqueAutomationRequest>();
    auto found = m_uniqueAutomationRequests.find(taskAssignmentSummary->getCorrespondingAutomationRequestID());
    if(found != m_uniqueAutomationRequests.end())
    {
        correspondingAutomationRequest = found->second;
    }
    else
    {
        std::string message = "ERROR::processTaskAssignmentSummary: Corresponding Unique Automation Request ID [";
        message += std::to_string(taskAssignmentSummary->getCorrespondingAutomationRequestID()) + "] not found!";
        sendError(message);
        return;
    }

    if (taskAssignmentSummary->getTaskList().empty())
    {
        std::string message = "No assignments found for request " + std::to_string(taskAssignmentSummary->getCorrespondingAutomationRequestID());
        sendError(message);
        return;
    }

    // ensure that a valid state for each vehicle in the request has been received
    for(auto v : correspondingAutomationRequest->getOriginalRequest()->getEntityList())
    {
        auto found = m_currentEntityStates.find(v);
        if(found == m_currentEntityStates.end())
        {
            std::string message = "ERROR::processTaskAssignmentSummary: Corresponding Unique Automation Request included vehicle ID [";
            message += std::to_string(v) + "] which does not have a corresponding current state!";
            sendError(message);
            return;
        }
    }

    // initialize state tracking maps with this corresponding request IDs
    m_assignmentSummaries[taskAssignmentSummary->getCorrespondingAutomationRequestID()] = taskAssignmentSummary;
    m_projectedEntityStates[taskAssignmentSummary->getCorrespondingAutomationRequestID()] = std::vector< std::shared_ptr<ProjectedState> >();
    m_remainingAssignments[taskAssignmentSummary->getCorrespondingAutomationRequestID()] = std::deque< std::shared_ptr<uxas::messages::task::TaskAssignment> >();
    m_inProgressResponse[taskAssignmentSummary->getCorrespondingAutomationRequestID()] = std::make_shared<uxas::messages::task::UniqueAutomationResponse>();
    m_inProgressResponse[taskAssignmentSummary->getCorrespondingAutomationRequestID()]->setResponseID(taskAssignmentSummary->getCorrespondingAutomationRequestID());

    // list all participating vehicles in the assignment
    std::vector<int64_t> participatingVehicles = correspondingAutomationRequest->getOriginalRequest()->getEntityList();
    if(participatingVehicles.empty())
    {
        for(auto v: m_currentEntityStates)
            participatingVehicles.push_back(v.first);
    }

    // load current participating vehicle states into projected state tracking
    for(auto vID : participatingVehicles)
    {
        auto entityState = m_currentEntityStates.find(vID)->second; // ensured to exist by above validation check
        auto projectedState = std::make_shared<ProjectedState>();
        projectedState->finalWaypointID = 0;
        projectedState->time = entityState->getTime();

        auto usePlanningState = std::find_if(correspondingAutomationRequest->getPlanningStates().begin(), correspondingAutomationRequest->getPlanningStates().end(),
                                            [&](uxas::messages::task::PlanningState* state) { return state->getEntityID() == vID; });
        if(usePlanningState != correspondingAutomationRequest->getPlanningStates().end())
        {
            projectedState->setState((*usePlanningState)->clone());
        }
        else
        {
            // add in the assignment start point lead distance
            auto planState = new uxas::messages::task::PlanningState;
            planState->setEntityID(vID);
            planState->setPlanningPosition(entityState->getLocation()->clone());
            planState->setPlanningHeading(entityState->getHeading());

            uxas::common::utilities::CUnitConversions unitConversions;
            double north_m(0.0);
            double east_m(0.0);
            unitConversions.ConvertLatLong_degToNorthEast_m(entityState->getLocation()->getLatitude(),
                                                            entityState->getLocation()->getLongitude(),
                                                            north_m, east_m);

            north_m += m_assignmentStartPointLead_m * cos(entityState->getHeading() * n_Const::c_Convert::dDegreesToRadians());
            east_m += m_assignmentStartPointLead_m * sin(entityState->getHeading() * n_Const::c_Convert::dDegreesToRadians());

            double latitude_deg(0.0);
            double longitude_deg(0.0);
            unitConversions.ConvertNorthEast_mToLatLong_deg(north_m, east_m, latitude_deg, longitude_deg);
            planState->getPlanningPosition()->setLatitude(latitude_deg);
            planState->getPlanningPosition()->setLongitude(longitude_deg);

            projectedState->setState(planState);
        }

        m_projectedEntityStates[taskAssignmentSummary->getCorrespondingAutomationRequestID()].push_back(projectedState);
    }

    // queue up all task assignments to be made
    for(auto t : taskAssignmentSummary->getTaskList())
    {
        m_remainingAssignments[taskAssignmentSummary->getCorrespondingAutomationRequestID()].push_back(std::shared_ptr<uxas::messages::task::TaskAssignment>(t->clone()));
    }

    sendNextTaskImplementationRequest(taskAssignmentSummary->getCorrespondingAutomationRequestID());
}

bool PlanBuilderService::sendNextTaskImplementationRequest(int64_t uniqueRequestID)
{
    if(m_uniqueAutomationRequests.find(uniqueRequestID) == m_uniqueAutomationRequests.end())
        return false;
    if(m_remainingAssignments[uniqueRequestID].empty())
        return false;
    auto taskAssignment = m_remainingAssignments[uniqueRequestID].front();

    auto planState = std::find_if(m_projectedEntityStates[uniqueRequestID].begin(), m_projectedEntityStates[uniqueRequestID].end(),
                                  [&](std::shared_ptr<ProjectedState> state)
                                  { return( (!state || !(state->state)) ? false : (state->state->getEntityID() == taskAssignment->getAssignedVehicle()) ); });
    if(planState == m_projectedEntityStates[uniqueRequestID].end())
        return false;
    if(!( (*planState)->state ) )
        return false;

    //std::cout << "taskAssignment->getOptionID(): " << taskAssignment->getOptionID() << std::endl;

    auto taskImplementationRequest = std::make_shared<uxas::messages::task::TaskImplementationRequest>();
    taskImplementationRequest->setCorrespondingAutomationRequestID(uniqueRequestID);
    m_expectedResponseID[m_taskImplementationId] = uniqueRequestID;
    taskImplementationRequest->setRequestID(m_taskImplementationId++);
    taskImplementationRequest->setStartingWaypointID( (*planState)->finalWaypointID + 1 );
    taskImplementationRequest->setVehicleID(taskAssignment->getAssignedVehicle());
    taskImplementationRequest->setTaskID(taskAssignment->getTaskID());
    taskImplementationRequest->setOptionID(taskAssignment->getOptionID());
    taskImplementationRequest->setRegionID(m_uniqueAutomationRequests[uniqueRequestID]->getOriginalRequest()->getOperatingRegion());
    taskImplementationRequest->setTimeThreshold(taskAssignment->getTimeThreshold());

    taskImplementationRequest->setStartHeading((*planState)->state->getPlanningHeading());
    taskImplementationRequest->setStartPosition((*planState)->state->getPlanningPosition()->clone());
    taskImplementationRequest->setStartTime((*planState)->time);

    for(auto neighbor : m_projectedEntityStates[uniqueRequestID])
    {
        if(neighbor && neighbor->state && neighbor->state->getEntityID() != (*planState)->state->getEntityID())
        {
            taskImplementationRequest->getNeighborLocations().push_back(neighbor->state->clone());
        }
    }

    m_remainingAssignments[uniqueRequestID].pop_front();
    sendSharedLmcpObjectBroadcastMessage(taskImplementationRequest);
    return true;
};

void PlanBuilderService::processTaskImplementationResponse(const std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse)
{
    // check response ID
    if(m_expectedResponseID.find(taskImplementationResponse->getResponseID()) == m_expectedResponseID.end())
        return;
    int64_t uniqueRequestID = m_expectedResponseID[taskImplementationResponse->getResponseID()];

    // cache response (waypoints in m_inProgressResponse)
    if(m_inProgressResponse.find(uniqueRequestID) == m_inProgressResponse.end())
        return;
    if(!m_inProgressResponse[uniqueRequestID])
        return;
    if(!m_inProgressResponse[uniqueRequestID]->getOriginalResponse())
        return;

    if(taskImplementationResponse->getTaskWaypoints().empty())
    {
        // task cannot be completed (e.g. inside a no-fly zone)
        std::string errMsg = "Task [" + std::to_string(taskImplementationResponse->getTaskID()) + "]";
        errMsg += " option [" + std::to_string(taskImplementationResponse->getOptionID()) + "]";
        errMsg += " assigned to vehicle [" + std::to_string(taskImplementationResponse->getVehicleID()) + "]";
        errMsg += " reported an empty waypoint list for implementation!";
        sendError(errMsg);

        // legacy: still try to complete the request, just skipping this task
        checkNextTaskImplementationRequest(uniqueRequestID);
        return;
    }

    auto corrMish = std::find_if(m_inProgressResponse[uniqueRequestID]->getOriginalResponse()->getMissionCommandList().begin(), m_inProgressResponse[uniqueRequestID]->getOriginalResponse()->getMissionCommandList().end(),
                                [&](afrl::cmasi::MissionCommand* mish) { return mish->getVehicleID() == taskImplementationResponse->getVehicleID(); });

    //std::cout << "TimeThreshold: " << taskImplementationResponse->getTimeThreshold() << std::endl;
    std::cout << "Outside TimeThreshold for " << std::to_string(taskImplementationResponse->getTaskID()) << " is: " << taskImplementationResponse->getTimeThreshold() << std::endl;
    if((taskImplementationResponse->getTimeThreshold() > 0) && (corrMish != m_inProgressResponse[uniqueRequestID]->getOriginalResponse()->getMissionCommandList().end())){
        std::cout << "Inside TimeThreshold for " << std::to_string(taskImplementationResponse->getTaskID()) << " is: " << taskImplementationResponse->getTimeThreshold() << std::endl;
        //create the loiter action for the task and set it to the first waypoint in the list

        afrl::cmasi::LoiterAction lTask;
        lTask.setDuration((int)taskImplementationResponse->getTimeThreshold()/1000); //THIS IS IN SECONDS, THE MDM IS WRONG!!!
        lTask.setLoiterType(afrl::cmasi::LoiterType::Circular);

        afrl::cmasi::Location3D locationToAdd;
        locationToAdd.setLatitude(taskImplementationResponse->getTaskWaypoints().front()->getLatitude());
        locationToAdd.setLongitude(taskImplementationResponse->getTaskWaypoints().front()->getLongitude());
        locationToAdd.setAltitude(taskImplementationResponse->getTaskWaypoints().front()->getAltitude());
        locationToAdd.setAltitudeType(taskImplementationResponse->getTaskWaypoints().front()->getAltitudeType());

        lTask.setLocation(locationToAdd.clone());
        //lTask.setLocation(m_currentEntityStates.find(taskImplementationResponse->getVehicleID())->second->getLocation()->clone());
        ////std::cout << lTask.getLocation()->toString() << std::endl;
        ////std::cout << lTask.toString() << std::endl;
        //std::cout << "Vehicle Action List: " << taskImplementationResponse->toString() << std::endl;
        //taskImplementationResponse->getTaskWaypoints().front()->getVehicleActionList().insert(taskImplementationResponse->getTaskWaypoints().front()->getVehicleActionList().begin(), lTask.clone());
        taskImplementationResponse->getTaskWaypoints().front()->getVehicleActionList().push_back(lTask.clone());
    }

    if(corrMish != m_inProgressResponse[uniqueRequestID]->getOriginalResponse()->getMissionCommandList().end())
    {
        std::cout << "Adding waypoints to an existing list" << std::endl;
        if(!(*corrMish)->getWaypointList().empty())
        {
            (*corrMish)->getWaypointList().back()->setNextWaypoint(taskImplementationResponse->getTaskWaypoints().front()->getNumber());
        }
        for(auto wp : taskImplementationResponse->getTaskWaypoints())
            (*corrMish)->getWaypointList().push_back(wp->clone());
    }
    else
    {
        auto mish = new afrl::cmasi::MissionCommand;
        mish->setCommandID(m_commandId++);
        mish->setVehicleID(taskImplementationResponse->getVehicleID());
        if(taskImplementationResponse->getTimeThreshold() > 0){
            afrl::cmasi::LoiterAction lTask;
            //So an issue currently is that thesetDuration is wanting seconds, not ms.
            //I added a cast from ms to seconds, but if/when this is fixed, the /1000 and cast to int should be removed
            lTask.setDuration((int)taskImplementationResponse->getTimeThreshold()/1000);
            lTask.setLoiterType(afrl::cmasi::LoiterType::Circular);
            lTask.setLocation(m_currentEntityStates.find(taskImplementationResponse->getVehicleID())->second->getLocation()->clone());
            taskImplementationResponse->getTaskWaypoints().front()->getVehicleActionList().insert(taskImplementationResponse->getTaskWaypoints().front()->getVehicleActionList().begin(), lTask.clone());

            afrl::cmasi::Location3D * locationToAdd = m_currentEntityStates.find(taskImplementationResponse->getVehicleID())->second->getLocation()->clone();
            taskImplementationResponse->getTaskWaypoints().front()->setLongitude(locationToAdd->getLongitude());
            taskImplementationResponse->getTaskWaypoints().front()->setLatitude(locationToAdd->getLatitude());
            taskImplementationResponse->getTaskWaypoints().front()->setAltitude(locationToAdd->getAltitude());
            taskImplementationResponse->getTaskWaypoints().front()->setAltitudeType(locationToAdd->getAltitudeType());

            ////std::cout << "Next waypoint: " << taskImplementationResponse->getTaskWaypoints().front()->getNextWaypoint() << std::endl;
            afrl::cmasi::Waypoint * newWP = taskImplementationResponse->getTaskWaypoints().front()->clone();

            ////std::cout << newWP->toString() << std::endl;
            newWP->setNextWaypoint(2);
            taskImplementationResponse->getTaskWaypoints().insert(taskImplementationResponse->getTaskWaypoints().begin(), newWP->clone());

            /* For bugfixing
            for(afrl::cmasi::Waypoint * wp : taskImplementationResponse->getTaskWaypoints()){
                //std::cout << wp->getNextWaypoint()-1 << "ActionList:" << std::endl;
                for(afrl::cmasi::VehicleAction * vhac : wp->getVehicleActionList()){
                    //std::cout << vhac->toString() << std::endl;
                }
            }
            */
        }
        ////std::cout << taskImplementationResponse->getTaskWaypoints().front()->toString() << std::endl;
        mish->setFirstWaypoint(taskImplementationResponse->getTaskWaypoints().front()->getNumber());
        for(auto wp : taskImplementationResponse->getTaskWaypoints())
            mish->getWaypointList().push_back(wp->clone());
        m_inProgressResponse[uniqueRequestID]->getOriginalResponse()->getMissionCommandList().push_back(mish);
    }

    // update project state (m_projectedEntityStates)
    if(m_projectedEntityStates.find(uniqueRequestID) != m_projectedEntityStates.end())
    {
        auto projectedState = std::find_if(m_projectedEntityStates[uniqueRequestID].begin(), m_projectedEntityStates[uniqueRequestID].end(),
                [&](std::shared_ptr<ProjectedState> state) { return ( (!state || !(state->state)) ? false : (state->state->getEntityID() == taskImplementationResponse->getVehicleID()) ); });
        if(projectedState != m_projectedEntityStates[uniqueRequestID].end())
        {
            (*projectedState)->finalWaypointID = taskImplementationResponse->getTaskWaypoints().back()->getNumber();
            (*projectedState)->time = taskImplementationResponse->getFinalTime();
            (*projectedState)->state->setPlanningPosition(taskImplementationResponse->getFinalLocation()->clone());
            (*projectedState)->state->setPlanningHeading(taskImplementationResponse->getFinalHeading());
        }
    }

    checkNextTaskImplementationRequest(uniqueRequestID);

};

void PlanBuilderService::checkNextTaskImplementationRequest(int64_t uniqueRequestID)
{
    // check to see if there are any more in the queue
    //    yes --> sendNextTaskImplementationRequest
    //    no --> send m_inProgressResponse[uniqueRequestID], then clear it out
    if(m_remainingAssignments.find(uniqueRequestID) != m_remainingAssignments.end())
    {
        if(m_remainingAssignments[uniqueRequestID].empty())
        {
            // add FinalStates (which are the 'projected' states in the planning process)
            if(m_projectedEntityStates.find(uniqueRequestID) != m_projectedEntityStates.end())
            {
                for(auto e : m_projectedEntityStates[uniqueRequestID])
                    if(e && e->state)
                        m_inProgressResponse[uniqueRequestID]->getFinalStates().push_back(e->state->clone());
            }
            sendSharedLmcpObjectBroadcastMessage(m_inProgressResponse[uniqueRequestID]);
            m_inProgressResponse.erase(uniqueRequestID);

            auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
            serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
            auto keyValuePair = new afrl::cmasi::KeyValuePair;
            std::string message = "UniqueAutomationResponse[" + std::to_string(uniqueRequestID) + "] - sent";
            keyValuePair->setKey(message);
            serviceStatus->getInfo().push_back(keyValuePair);
            sendSharedLmcpObjectBroadcastMessage(serviceStatus);
        }
        else
        {
            sendNextTaskImplementationRequest(uniqueRequestID);
        }
    }
}

}; //namespace service
}; //namespace uxas

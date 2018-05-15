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
#include "FlatEarth.h"
#include "RouteExtension.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "uxas/messages/task/RendezvousTask.h"
#include "afrl/cmasi/VehicleActionCommand.h"
#include "uxas/messages/uxnative/SpeedOverrideAction.h"

namespace uxas
{
namespace service
{
namespace task
{

// this entry registers the service in the service creation registry
RendezvousTask::ServiceBase::CreationRegistrar<RendezvousTask>
RendezvousTask::s_registrar(RendezvousTask::s_registryServiceTypeNames());

// service constructor
RendezvousTask::RendezvousTask()
: TaskServiceBase(RendezvousTask::s_typeName(), RendezvousTask::s_directoryName())
{
    m_isMakeTransitionWaypointsActive = true; // to allow for speed changes
}

RendezvousTask::~RendezvousTask() { }

bool
RendezvousTask::configureTask(const pugi::xml_node& ndComponent)
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Configuring Rendezvous Task!" );
    
    // add subscription to TaskAssignmentSummary to determine the complete
    // set of vehicles assigned to this task
    addSubscriptionAddress(uxas::messages::task::TaskAssignmentSummary::Subscription);
    
    // add subscription to AssignmentCostMatrix to determine timing between options
    addSubscriptionAddress(uxas::messages::task::AssignmentCostMatrix::Subscription);
    
    return true;
}
    
bool RendezvousTask::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
{
    if(uxas::messages::task::isTaskAssignmentSummary(receivedLmcpObject))
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
        auto assignSummary = std::static_pointer_cast<uxas::messages::task::TaskAssignmentSummary>(receivedLmcpObject);
        m_assignmentSummary[assignSummary->getCorrespondingAutomationRequestID()] = assignSummary;
    }
    else if(uxas::messages::task::isAssignmentCostMatrix(receivedLmcpObject))
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
        auto assignCostMatrix = std::static_pointer_cast<uxas::messages::task::AssignmentCostMatrix>(receivedLmcpObject);
        m_assignmentCostMatrix[assignCostMatrix->getCorrespondingAutomationRequestID()] = assignCostMatrix;
    }
    else if(uxas::messages::task::isTaskImplementationRequest(receivedLmcpObject))
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
        auto implReq = std::static_pointer_cast<uxas::messages::task::TaskImplementationRequest>(receivedLmcpObject);
        updateStartTimes(implReq);
    }
    else if(uxas::messages::task::isTaskImplementationResponse(receivedLmcpObject))
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
        auto implResp = std::static_pointer_cast<uxas::messages::task::TaskImplementationResponse>(receivedLmcpObject);
        updateStartTimes(implResp);
    }
    else if(uxas::messages::task::isUniqueAutomationRequest(receivedLmcpObject))
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
        auto uReq = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpObject);
        m_sandboxRequest[uReq->getRequestID()] = uReq->getSandBoxRequest();
    }
    else if(uxas::messages::task::isUniqueAutomationResponse(receivedLmcpObject))
    {
        // TODO, clear memory associated with interim calculations, ie AssignmentCostMatrix and AssigmentSummary
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
        auto uResp = std::static_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(receivedLmcpObject);
        if(m_sandboxRequest.find(uResp->getResponseID()) != m_sandboxRequest.end())
        {
            if(!m_sandboxRequest[uResp->getResponseID()])
            {
                // latch in the planned TOA to assigned TOA
                if(m_plannedToa.find(uResp->getResponseID()) != m_plannedToa.end())
                {
                    m_assignedToa = m_plannedToa[uResp->getResponseID()];
                }
            }
        }
    }
    
    return false;
}

void RendezvousTask::updateStartTimes(std::shared_ptr<uxas::messages::task::TaskImplementationRequest>& implReq)
{
    int64_t rID = implReq->getCorrespondingAutomationRequestID();
    int64_t vID = implReq->getVehicleID();
    m_taskStartTime[rID][vID] = implReq->getStartTime();

    // assume that all vehicles start when the first vehicle starts
    if(m_assignmentSummary.find(rID) == m_assignmentSummary.end()) return;
    
    for(auto v : m_assignmentSummary[rID]->getTaskList())
        if(m_taskStartTime[rID].find(v->getAssignedVehicle()) == m_taskStartTime[rID].end())
            m_taskStartTime[rID][v->getAssignedVehicle()] = implReq->getStartTime();
}

void RendezvousTask::updateStartTimes(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& implResp)
{
    int64_t rID = implResp->getCorrespondingAutomationRequestID();
    int64_t vID = implResp->getVehicleID();
    if(implResp->getTaskID() != m_task->getTaskID())
        m_taskStartTime[rID][vID] = implResp->getFinalTime();
}

void RendezvousTask::buildTaskPlanOptions()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task building options!");
    
    int64_t taskId(m_task->getTaskID());
    int64_t optionId = TaskOptionClass::m_firstOptionId;
    auto rtask = std::static_pointer_cast<uxas::messages::task::RendezvousTask>(m_task);
    // key: vehicle ID, value: corresponding option IDs
    std::unordered_map<int64_t, std::vector<int64_t> > optionMap;
    
    // add option(s) for every eligible entity
    for (auto itEligibleEntities = m_speedAltitudeVsEligibleEntityIds.begin();
            itEligibleEntities != m_speedAltitudeVsEligibleEntityIds.end();
            itEligibleEntities++)
    {
        for (auto v : itEligibleEntities->second)
        {
            if(!rtask->getMultiLocationRendezvous())
            {
                if(!rtask->getLocation()) break;
                auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
                auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
                pTaskOptionClass->m_taskOption->setTaskID(taskId);
                pTaskOptionClass->m_taskOption->setOptionID(optionId);
                pTaskOptionClass->m_taskOption->setCost(0);
                pTaskOptionClass->m_taskOption->setStartLocation(rtask->getLocation()->clone());
                pTaskOptionClass->m_taskOption->setStartHeading(rtask->getHeading());
                pTaskOptionClass->m_taskOption->setEndLocation(rtask->getLocation()->clone());
                pTaskOptionClass->m_taskOption->setEndHeading(rtask->getHeading());
                pTaskOptionClass->m_taskOption->getEligibleEntities().push_back(v);
                m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
                m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());
                optionMap[v].push_back(optionId);
                optionId++;
            }
            else
            {
                for(auto planstate : rtask->getRendezvousStates())
                {
                    if(planstate->getEntityID() == 0 || planstate->getEntityID() == v)
                    {
                        auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
                        auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
                        pTaskOptionClass->m_taskOption->setTaskID(taskId);
                        pTaskOptionClass->m_taskOption->setOptionID(optionId);
                        pTaskOptionClass->m_taskOption->setCost(0);
                        pTaskOptionClass->m_taskOption->setStartLocation(planstate->getPlanningPosition()->clone());
                        pTaskOptionClass->m_taskOption->setStartHeading(planstate->getPlanningHeading());
                        pTaskOptionClass->m_taskOption->setEndLocation(planstate->getPlanningPosition()->clone());
                        pTaskOptionClass->m_taskOption->setEndHeading(planstate->getPlanningHeading());
                        pTaskOptionClass->m_taskOption->getEligibleEntities().push_back(v);
                        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
                        m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());
                        optionMap[v].push_back(optionId);
                        optionId++;
                    }
                }
            }
        }
    }
    
    // build options for each vehicle
    std::vector< std::string > vehicleOptionStr;
    for(auto vID : optionMap)
    {
        std::string voptions = "";
        if(vID.second.size() > 1) voptions += " +(";
        for(auto oID : vID.second)
        {
            voptions += "p";
            voptions += std::to_string(oID);
            voptions += " ";
        }
        if(vID.second.size() > 1) voptions += ")";
        vehicleOptionStr.push_back(voptions);
    }
    
    // format composition string to ensure proper groups of vehicles are considered
    std::string compositionString;
    if(rtask->getNumberOfParticipants() >= optionMap.size())
    {
        // all vehicles are involved, simply iterate through each
        compositionString = ".(";
        for(auto vs : vehicleOptionStr)
            compositionString += vs;
        compositionString += ")";
    }
    else
    {
        // create all subsets of eligible entities of size rtask->getNumberOfParticipants()
        // TODO actually build N choose K compositions, for now just add the first subset
        compositionString = ".(";
        size_t s = 0;
        for(auto vs : vehicleOptionStr)
        {
            compositionString += vs;
            s++;
            if(s >= rtask->getNumberOfParticipants()) break;
        }
        compositionString += ")";
    }
    
    m_taskPlanOptions->setComposition(compositionString);
    sendSharedLmcpObjectBroadcastMessage(m_taskPlanOptions);
    
}

bool RendezvousTask::isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
                std::shared_ptr<TaskOptionClass>& taskOptionClass,
                int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route)
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task processing route response!");
    
    auto rtask = std::static_pointer_cast<uxas::messages::task::RendezvousTask>(m_task);
    if(taskImplementationResponse->getTaskWaypoints().empty()) return false;
    
    auto wp = taskImplementationResponse->getTaskWaypoints().at(0);
    if(wp->getSpeed() < 1e-4) return false;
    double V = wp->getSpeed();
    
    // look up timing for each vehicle involved in the task
    auto assignsummary = m_assignmentSummary.find(taskImplementationResponse->getCorrespondingAutomationRequestID());
    if(assignsummary == m_assignmentSummary.end()) return false;
    auto assignmatrix = m_assignmentCostMatrix.find(taskImplementationResponse->getCorrespondingAutomationRequestID());
    if(assignmatrix == m_assignmentCostMatrix.end()) return false;
    auto startTimes = m_taskStartTime.find(taskImplementationResponse->getCorrespondingAutomationRequestID());
    if(startTimes == m_taskStartTime.end()) return false;
    auto requestedStartTime = startTimes->second.find(taskImplementationResponse->getVehicleID());
    if(requestedStartTime == startTimes->second.end()) return false;
    
    // identify vehicles involved in this task
    std::unordered_map<int64_t, std::pair<int64_t, int64_t> > prevTaskOptionPair;
    std::unordered_map<int64_t, int64_t> selectedOption;
    for(auto ta : assignsummary->second->getTaskList())
    {
        if(ta->getTaskID() == m_task->getTaskID())
        {
            selectedOption[ta->getAssignedVehicle()] = ta->getOptionID();
        }
        else if(selectedOption.find(ta->getAssignedVehicle()) == selectedOption.end())
        {
            prevTaskOptionPair[ta->getAssignedVehicle()] = std::make_pair(ta->getTaskID(),ta->getOptionID());
        }
    }
    
    int64_t maxArrivalTime = 0;
    int64_t maxArrivalVehicle = 0;
    for(auto option : selectedOption)
    {
        auto prevOption = prevTaskOptionPair.find(option.first);
        std::pair<int64_t,int64_t> optionPair = std::make_pair(0,0);
        if(prevOption != prevTaskOptionPair.end())
        {
            optionPair = prevOption->second;
        }
        
        for(auto optioncost : assignmatrix->second->getCostMatrix())
        {
            if(optioncost->getVehicleID() == option.first
                && optioncost->getDestinationTaskID() == m_task->getTaskID()
                && optioncost->getDestinationTaskOption() == option.second
                && optioncost->getIntialTaskID() == optionPair.first
                && optioncost->getIntialTaskOption() == optionPair.second)
            {
                int64_t arrivalTime = 0;
                auto vehicleStartTime = startTimes->second.find(option.first);
                if(vehicleStartTime == startTimes->second.end())
                {
                    // look up from state message
                    auto avstate = m_entityStates.find(taskImplementationResponse->getVehicleID());
                    if(avstate == m_entityStates.end()) continue;
                    arrivalTime = optioncost->getTimeToGo() + avstate->second->getTime();
                }
                else
                    arrivalTime = optioncost->getTimeToGo() + vehicleStartTime->second;
                
                if(arrivalTime > maxArrivalTime)
                {
                    maxArrivalTime = arrivalTime;
                    maxArrivalVehicle = option.first;
                }
            }
        }
    }
    
    if(maxArrivalVehicle == taskImplementationResponse->getVehicleID())
        return true;

    // need to extend path, calculate actual path length
    uxas::common::utilities::FlatEarth flatEarth;
    double north, east;
    flatEarth.ConvertLatLong_degToNorthEast_m(wp->getLatitude(), wp->getLongitude(), north, east);
    double travelDist = 0.0;
    for(size_t w=1; w<taskImplementationResponse->getTaskWaypoints().size(); w++)
    {
        wp = taskImplementationResponse->getTaskWaypoints().at(w);
        double next_north, next_east;
        flatEarth.ConvertLatLong_degToNorthEast_m(wp->getLatitude(), wp->getLongitude(), next_north, next_east);
        travelDist += sqrt( (next_north-north)*(next_north-north) + (next_east-east)*(next_east-east) );
        north = next_north;
        east = next_east;
    }

    // calculate extension time
    int64_t extendTime_ms = maxArrivalTime - static_cast<int64_t>(travelDist/V*1000) - requestedStartTime->second;
    m_plannedToa[taskImplementationResponse->getCorrespondingAutomationRequestID()][taskImplementationResponse->getVehicleID()] = maxArrivalTime;
    
    if(extendTime_ms <= 1000) return true;

    // extend waypoints, hard-coded to 280m radius, 200m minimum segment size
    return uxas::common::utilities::RouteExtension::ExtendPath(taskImplementationResponse->getTaskWaypoints(), extendTime_ms, 280.0, 200.0);
}

void RendezvousTask::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    auto entconfig = m_entityConfigurations.find(entityState->getID());
    if(entconfig == m_entityConfigurations.end()) return;
    auto avconfig = std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(entconfig->second);
    if(!avconfig) return;

    double speedMin_mps = avconfig->getMinimumSpeed();
    double speedMax_mps = avconfig->getMaximumSpeed();

    auto mission_wps = m_currentMissions.find(entityState->getID());
    if(mission_wps == m_currentMissions.end()) return;
    auto wplist = mission_wps->second->getWaypointList();

    uxas::common::utilities::FlatEarth flatEarth;
    double north, east;
    flatEarth.ConvertLatLong_degToNorthEast_m(entityState->getLocation()->getLatitude(), entityState->getLocation()->getLongitude(), north, east);

    double remainingDist = 0.0;
    auto indx = FindWaypointIndex(wplist, entityState->getCurrentWaypoint());
    while(indx < wplist.size())
    {
        auto wp = wplist.at(indx);
        if(std::find(wp->getAssociatedTasks().begin(), wp->getAssociatedTasks().end(), m_task->getTaskID()) == wp->getAssociatedTasks().end())
            break;

        double next_north, next_east;
        flatEarth.ConvertLatLong_degToNorthEast_m(wp->getLatitude(), wp->getLongitude(), next_north, next_east);

        remainingDist += sqrt( (next_north-north)*(next_north-north) + (next_east-east)*(next_east-east) );
        north = next_north;
        east = next_east;
        indx = FindWaypointIndex(wplist, wp->getNextWaypoint());
    }

    // remaining time
    int64_t rtime = 0;
    if(m_assignedToa.find(entityState->getID()) != m_assignedToa.end())
    {
        rtime = m_assignedToa[entityState->getID()] - entityState->getTime();
    }

    if(rtime < 1000 || remainingDist < 1.0) return;

    // speed to reach target on time
    double desired_speed = (std::max)(speedMin_mps, (std::min)(speedMax_mps, remainingDist/(rtime/1000.0)));

    auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
    vehicleActionCommand->setVehicleID(entityState->getID());
    auto s = new uxas::messages::uxnative::SpeedOverrideAction;
    s->setVehicleID(entityState->getID());
    s->setSpeed(desired_speed);
    s->getAssociatedTaskList().push_back(m_task->getTaskID());
    vehicleActionCommand->getVehicleActionList().push_back(s);
    sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);
}

size_t RendezvousTask::FindWaypointIndex(const std::vector<afrl::cmasi::Waypoint*> wplist, int64_t wpid)
{
    for(size_t x=0; x<wplist.size(); x++)
    {
        if(wplist.at(x)->getNumber() == wpid)
            return x;
    }
    return wplist.size();
}
    
} //namespace task
} //namespace service
} //namespace uxas

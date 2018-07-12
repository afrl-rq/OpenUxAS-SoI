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
    auto vstate = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpObject);
    if(vstate)
    {
        // update 'remaining distance' list
        m_distanceRemaining[vstate->getID()] = std::make_pair(vstate->getTime(), ArrivalDistance(vstate));
    }
    else if(uxas::messages::task::isTaskAssignmentSummary(receivedLmcpObject))
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
    else if(uxas::messages::task::isUniqueAutomationResponse(receivedLmcpObject))
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task handling: ", receivedLmcpObject->getFullLmcpTypeName());
        auto uResp = std::static_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(receivedLmcpObject);
        
        // clear memory associated with interim calculations
        m_assignmentSummary.erase(uResp->getResponseID());
        m_assignmentCostMatrix.erase(uResp->getResponseID());
        m_taskStartTime.erase(uResp->getResponseID());
    }
    
    return false;
}

void RendezvousTask::updateStartTimes(std::shared_ptr<uxas::messages::task::TaskImplementationRequest>& implReq)
{
    // Track the 'time on mission' that each vehicle will have before reaching
    // the rendezvous task. This ASSUMES the following:
    // Implementation requests are sent in order, so all tasks scheduled before
    // this task will have had implementation requests sent
    
    // Update this vehicles' start time
    int64_t rID = implReq->getCorrespondingAutomationRequestID();
    int64_t vID = implReq->getVehicleID();
    m_taskStartTime[rID][vID] = implReq->getStartTime();

    // ensure that a corresponding assignment summary has previously been sent
    if(m_assignmentSummary.find(rID) == m_assignmentSummary.end()) return;
    
    // if any vehicle in the assignment doesn't have a start time, simply
    // assume that it starts at this time of the first vehicle that received
    // a task implementation request
    for(auto v : m_assignmentSummary[rID]->getTaskList())
        if(m_taskStartTime[rID].find(v->getAssignedVehicle()) == m_taskStartTime[rID].end())
            m_taskStartTime[rID][v->getAssignedVehicle()] = implReq->getStartTime();
}

void RendezvousTask::updateStartTimes(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& implResp)
{
    // Dual to the task implementation request: update the time if that vehicle
    // was part of a task whose implementation is reported. This also ASSUMES
    // that task implementation proceeds in order of assignment
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
    
    // Add a zero cost option for every eligible entity at the desired
    // location and orientation of the rendezvous - extensions to routes
    // to meet timing synchronization will be handled after assignment
    // during the implementation phase
    for (auto itEligibleEntities = m_speedAltitudeVsEligibleEntityIds.begin();
            itEligibleEntities != m_speedAltitudeVsEligibleEntityIds.end();
            itEligibleEntities++)
    {
        for (auto v : itEligibleEntities->second)
        {
            if(!rtask->getMultiLocationRendezvous())
            {
                // plan for each vehicle to meet at the same location
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
                // add an option for each distinct desired state at rendezvous
                for(auto planstate : rtask->getRendezvousStates())
                {
                    // these can be vehicle specific or for any vehicle (0 ID)
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
        if(vID.second.size() > 1) voptions += "+( ";
        for(auto oID : vID.second)
        {
            voptions += "p";
            voptions += std::to_string(oID);
            voptions += " ";
        }
        if(vID.second.size() > 1) voptions += ") ";
        vehicleOptionStr.push_back(voptions);
    }
    
    // format composition string to ensure proper groups of vehicles are considered
    std::string compositionString;
    if(rtask->getNumberOfParticipants() >= optionMap.size())
    {
        // all vehicles are involved, simply iterate through each
        compositionString = ".( ";
        for(auto vs : vehicleOptionStr)
            compositionString += vs;
        compositionString += ")";
    }
    else
    {
        // N choose K combinations of vehicles to desired end states
        // limit to max number so as to not explode assignment problem
        // note: for repeatability, deterministically list through combinations
        // even though random choices may lead to better performance when
        // limiting the number of combinations considered
        uint8_t N = vehicleOptionStr.size();          // available vehicles
        uint8_t K = rtask->getNumberOfParticipants(); // desired set size
        uint8_t T = 64; // max limit of returned combinations
        uint8_t t = 0;  // current number of combinations
        
        // technique: permute bitmask of 'involved' vehicles
        // see https://rosettacode.org/wiki/Combinations#C.2B.2B
        std::string bitmask(K, 1); // K leading 1's
        bitmask.resize(N, 0);      // N-K trailing 0's

        compositionString = "+( ";
        do {
            compositionString += ".( ";
            for(int i=0; i < N; i++)
                if(bitmask[i])
                    compositionString += vehicleOptionStr[i];
            compositionString += ") ";
            t++;
        } while (std::prev_permutation(bitmask.begin(), bitmask.end()) && t < T);
        compositionString += ") ";
    }
    
    m_taskPlanOptions->setComposition(compositionString);
    sendSharedLmcpObjectBroadcastMessage(m_taskPlanOptions);
    
}

bool RendezvousTask::isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
                std::shared_ptr<TaskOptionClass>& taskOptionClass,
                int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route)
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), " Rendezvous Task processing route response!");
    
    if(taskImplementationResponse->getTaskWaypoints().empty()) return false; 
    auto wp = taskImplementationResponse->getTaskWaypoints().at(0);
    if(!wp) return false;
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

    // need to extend path, calculate actual path length
    uxas::common::utilities::FlatEarth flatEarth;
    flatEarth.Initialize(wp->getLatitude()*n_Const::c_Convert::dDegreesToRadians(),
                         wp->getLongitude()*n_Const::c_Convert::dDegreesToRadians());
    
    double travelDist = 0.0;
    double north{0.0}, east{0.0};
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
    if(extendTime_ms <= 1000 || maxArrivalVehicle == taskImplementationResponse->getVehicleID()) return true;

    std::cout << "Extending route for " << taskImplementationResponse->getVehicleID() << " by amount (ms) " << extendTime_ms << std::endl;
    
    // extend waypoints, hard-coded to 280m radius, 200m minimum segment size
    bool e = uxas::common::utilities::RouteExtension::ExtendPath(taskImplementationResponse->getTaskWaypoints(), extendTime_ms, 200.0, 150.0);
    if(!e)
    {
        std::cout << "  extension failed, trying full circle" << std::endl;
        uxas::common::utilities::RouteExtension::ExtendPath(taskImplementationResponse->getTaskWaypoints(), 1000*2*3.1415*200/V+1000, 200.0, 150.0);
    }
    return true;    
}

std::pair<double, double> RendezvousTask::SpeedClip(const std::shared_ptr<afrl::cmasi::AirVehicleConfiguration>& avconfig, double& nomSpeed)
{
    if(!avconfig)
        return std::make_pair(nomSpeed, nomSpeed);
    
    double speedMin = avconfig->getMinimumSpeed();
    double speedMax = avconfig->getMaximumSpeed();
    double speedNom = avconfig->getNominalSpeed();
    if(speedNom < 1e-4) speedNom = nomSpeed;
    else nomSpeed = speedNom;
    if(speedMin < 1e-4 || speedMin > nomSpeed) speedMin = nomSpeed;
    if(speedMax < nomSpeed) speedMax = nomSpeed;
    
    return std::make_pair(speedMin, speedMax);
}

void RendezvousTask::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    auto entconfig = m_entityConfigurations.find(entityState->getID());
    if(entconfig == m_entityConfigurations.end()) return;
    auto avconfig = std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(entconfig->second);
    if(!avconfig) return;

    double speedNom_mps = avconfig->getNominalSpeed();
    if(speedNom_mps < 1e-4) speedNom_mps = entityState->getGroundspeed();
    if(speedNom_mps < 1e-4) return;
    auto speedInterval = SpeedClip(avconfig, speedNom_mps);

    // feasible time interval
    double remainingDist = ArrivalDistance(entityState);
    int64_t midtime = remainingDist/speedNom_mps*1000;
    int64_t maxtime = remainingDist/speedInterval.first*1000;
    int64_t mintime = remainingDist/speedInterval.second*1000;
    std::vector<int64_t> desiredTimes;
    desiredTimes.push_back(midtime);
    
    // use 'm_distanceRemaining' to select current speed to travel
    // assuming neighbor with largest remaining distance travels
    // at the same nominal speed
    for(auto neighbor : m_distanceRemaining)
    {
        // if there's no valid distance remaining, just ignore
        if(neighbor.second.second < speedNom_mps) continue;
        if(neighbor.first == entityState->getID()) continue; // already added
        
        // find speed window for neighbor
        auto nconfig = m_entityConfigurations.find(neighbor.first);
        if(entconfig == m_entityConfigurations.end()) continue;
        auto navconfig = std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(nconfig->second);
        double nspeedNom = speedNom_mps;
        auto neighborInterval = SpeedClip(navconfig, nspeedNom);
        
        // time elapsed between 'now' and when the distance was calculated
        int64_t dt = entityState->getTime() - neighbor.second.first;
        if(dt < 0) dt = 0; // this shouldn't happen
        
        // estimated time of arrival is dist/speed then subtracting
        // time that neighbor vehicle has already been traveling
        int64_t nmidTime = neighbor.second.second/nspeedNom*1000 - dt;
        int64_t nmaxTime = neighbor.second.second/neighborInterval.first*1000 - dt;
        int64_t nminTime = neighbor.second.second/neighborInterval.second*1000 - dt;
        
        // only consider this neighbor if further than 1 second out
        // and less than 5 seconds stale
        if(nmidTime > 1000 && dt < 5000)
        {
            desiredTimes.push_back(nmidTime);
            // shrink feasible time window based on this neighbors capability
            if(nmaxTime < maxtime) maxtime = nmaxTime;
            if(nminTime > mintime) mintime = nminTime;
        }
    }
    
    // if no feasible window, just get as close to center of 'infeasible' area
    int64_t rtime = (mintime - maxtime)/2;
    if(mintime <= maxtime)
    {
        // there is a feasible window, so optimize rendezvous time to be
        // as close as possible to nominal speeds for involved vehicles
        // let the cost for each vehicle be the square of the difference in
        // time between the nominal time of arrival and a particular rendezvous
        // time --> J = sum_{1,N} (r - t_n)^2 where t_n is the nominal time
        // for vehicle 'n' and r is the candidate rendezvous time
        // a local minimum will be when the derivative of J is zero, i.e.
        // 0 = sum_{1,N} 2*(r - t_n) ==> r = 1/N * sum_{1,N} t_n
        // in other words, for quadratic cost, the optimal arrival time is the
        // average of the nominal times for each vehicle involved
        rtime = 0;
        for(auto t : desiredTimes)
            rtime += t;
        rtime /= desiredTimes.size();
        // clamp to feasible window
        rtime = (std::max)(mintime, (std::min)(maxtime, rtime));
    }
    
    if(entityState->getID() == m_entityId)
    {
        for(auto dst : desiredTimes)
            std::cout << "      ntime: " << dst << std::endl;
        std::cout << "    mintime: " << mintime << std::endl;
        std::cout << "    maxtime: " << maxtime << std::endl;
        std::cout << "    destime: " << midtime << std::endl;
        std::cout << "      rtime: " << rtime << std::endl;
        std::cout << "Entity [" << m_entityId << "] has rtime: " << rtime << " and rdist: " << remainingDist << std::endl;
    }

    double desired_speed = speedNom_mps;
    // if we're within one second of the target just coast at nominal,
    // as it's too late for fine adjustments
    if(rtime > 1000 && remainingDist > speedNom_mps)
        desired_speed = (std::max)(speedInterval.first, (std::min)(speedInterval.second, remainingDist/(rtime/1000.0)));
    
    // desired speed will get to the target at the rendezvous time, assuming
    // nothing changes; but, would like to make progress towards nominal speed,
    // use proportional control to converge to nominal speed
    desired_speed += 2.0*(desired_speed - speedNom_mps);
    desired_speed = (std::max)(speedInterval.first, (std::min)(speedInterval.second, desired_speed));
    
    if(entityState->getID() == m_entityId)
        std::cout << "Commanding [" << m_entityId << "] to speed: " << desired_speed << " with current speed: " << entityState->getGroundspeed() << std::endl;
    
    auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
    vehicleActionCommand->setVehicleID(entityState->getID());
    auto s = new uxas::messages::uxnative::SpeedOverrideAction;
    s->setVehicleID(entityState->getID());
    s->setSpeed(desired_speed);
    s->getAssociatedTaskList().push_back(m_task->getTaskID());
    vehicleActionCommand->getVehicleActionList().push_back(s);
    sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);
}
    
double RendezvousTask::ArrivalDistance(const std::shared_ptr<afrl::cmasi::EntityState>& state)
{
    // utilizes latest information from expected waypoints
    // to estimate distance remaining to rendezvous location
    
    if(!m_task) return 0.0;
    if(!state) return 0.0;
    if(!state->getLocation()) return 0.0;
    int64_t vID = state->getID();
    if(m_currentMissions.find(vID) == m_currentMissions.end()) return 0.0; 
    
    uxas::common::utilities::FlatEarth flatEarth;
    flatEarth.Initialize(state->getLocation()->getLatitude()*n_Const::c_Convert::dDegreesToRadians(),
                         state->getLocation()->getLongitude()*n_Const::c_Convert::dDegreesToRadians());
    
    auto wplist = m_currentMissions[vID]->getWaypointList();    
    auto indx = FindWaypointIndex(wplist, state->getCurrentWaypoint());
    std::unordered_set<size_t> loopDetect;
    loopDetect.insert(indx);
    
    double remainingDist = 0.0;
    double north{0.0}, east{0.0};
    while(indx < wplist.size())
    {
        auto wp = wplist.at(indx);
        if(!wp) break;
        if(std::find(wp->getAssociatedTasks().begin(), wp->getAssociatedTasks().end(), m_task->getTaskID()) == wp->getAssociatedTasks().end())
            break;

        double next_north, next_east;
        flatEarth.ConvertLatLong_degToNorthEast_m(wp->getLatitude(), wp->getLongitude(), next_north, next_east);

        remainingDist += sqrt( (next_north-north)*(next_north-north) + (next_east-east)*(next_east-east) );
        north = next_north;
        east = next_east;
        indx = FindWaypointIndex(wplist, wp->getNextWaypoint());
        if(loopDetect.find(indx) != loopDetect.end())
            break;
        loopDetect.insert(indx);
    }
    
    return remainingDist;
}
    
size_t RendezvousTask::FindWaypointIndex(const std::vector<afrl::cmasi::Waypoint*> wplist, int64_t wpid)
{
    for(size_t x=0; x<wplist.size(); x++)
    {
        if(wplist.at(x) && wplist.at(x)->getNumber() == wpid)
            return x;
    }
    return wplist.size();
}
    
} //namespace task
} //namespace service
} //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_Base.cpp
 * Author: steve
 * 
 * Created on September 2, 2015, 4:17 PM
 */

#include "TaskServiceBase.h"

#include "UnitConversions.h"
#include "FileSystemUtilities.h"

#include "Dpss.h"    //from OHARA

#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityConfigurationDescendants.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/EntityStateDescendants.h"
#include "avtas/lmcp/LmcpXMLReader.h"
#include "uxas/messages/task/TaskComplete.h"
#include "uxas/messages/task/TaskInitialized.h"
#include "uxas/messages/task/TaskActive.h"

#include <algorithm>      //std::find_if
#include <sstream>      //std::stringstream
#include <iomanip>  //setfill

#define MAX_TOTAL_COST_MS (INT64_MAX / 1000)
#define STRING_XML_TYPE "Type"

namespace uxas
{
namespace service
{
namespace task
{

#define COUT_INFO_MSG(MESSAGE) std::cout << "<>Task_Base::"  << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>Task_Base:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>Task_Base:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


const int64_t TaskOptionClass::m_firstOptionId{10}; // starting option of the tasks.  */
const int64_t TaskOptionClass::m_routeIdFromLastTask{1}; // id of the route from the last position to the start of this task option  
const int64_t TaskOptionClass::m_firstImplementationRouteId{2}; // first id to use for the routes in this task option
//XML STRINGS    
const std::string TaskServiceBase::m_taskOptions_XmlTag{"TaskOptions"};

bool isColocated(afrl::cmasi::Location3D* a, afrl::cmasi::Location3D* b)
{
    if(!a || !b) return false;

    if( fabs(a->getLatitude() - b->getLatitude()) < 1e-6 &&
        fabs(a->getLongitude() - b->getLongitude()) < 1e-6 )
        return true;
    return false;
}

TaskOptionClass::TaskOptionClass(std::shared_ptr<uxas::messages::task::TaskOption>& taskOption)
: m_taskOption(taskOption)
{
};

TaskServiceBase::TaskServiceBase(const std::string& typeName, const std::string& directoryName)
: ServiceBase(typeName, directoryName)
{
    //    COUT_INFO_MSG("Task Type[" << typeName << "] m_serviceId[" << m_serviceId << "] CREATED")
}

TaskServiceBase::~TaskServiceBase()
{
    if (m_task)
    {
        //        COUT_INFO_MSG("TaskID[" << m_task->getTaskID() << "] m_serviceId[" << m_serviceId << "] DESTROYED")
    }
};

bool TaskServiceBase::configure(const pugi::xml_node& serviceXmlNode)
{
    bool isSuccessful(true);

    if (m_workDirectoryPath.empty())
    {
        m_workDirectoryPath = "./";
    }

    m_task = generateTaskObject(serviceXmlNode);
    if (!m_task)
    {
        std::stringstream sstrErrors;
        sstrErrors << "ERROR:: **Task_Base::bConfigure failed: could find a task in [" << serviceXmlNode.name() << "]" << std::endl;
        CERR_FILE_LINE_MSG(sstrErrors.str())
        isSuccessful = false;
    }

    //double check sane Ground Sample Distance
    auto searchTask = std::dynamic_pointer_cast<afrl::cmasi::SearchTask>(m_task);
    if (searchTask) {
        if (searchTask->getGroundSampleDistance() < 0.01) {
            searchTask->setGroundSampleDistance(1000); 
        }
    }
    
    for (pugi::xml_node currentXmlNode = serviceXmlNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
    {
        if (currentXmlNode.attribute("Series").empty())
            continue;

        std::stringstream stringStream;
        currentXmlNode.print(stringStream);
        avtas::lmcp::Object* object = avtas::lmcp::xml::readXML(stringStream.str());
        if (object == nullptr)
            continue;

        if (dynamic_cast<afrl::cmasi::EntityConfiguration*> (object))
        {
            std::shared_ptr<afrl::cmasi::EntityConfiguration> entityConfiguration;
            entityConfiguration.reset(static_cast<afrl::cmasi::EntityConfiguration*> (object->clone()));
            auto foundEntity = std::find(m_task->getEligibleEntities().begin(), m_task->getEligibleEntities().end(), entityConfiguration->getID());
            if (m_task->getEligibleEntities().empty() || foundEntity != m_task->getEligibleEntities().end())
            {
                m_entityConfigurations.insert(std::make_pair(entityConfiguration->getID(), entityConfiguration));
                auto nominalSpeedToOneDecimalPlace_mps = std::round(entityConfiguration->getNominalSpeed()*10.0) / 10.0;
                auto nominalAltitudeRounded = std::round(entityConfiguration->getNominalAltitude());
                auto targetEntityIds = m_speedAltitudeVsEligibleEntityIds[std::make_pair(nominalSpeedToOneDecimalPlace_mps, nominalAltitudeRounded)];
                if (std::find(targetEntityIds.begin(), targetEntityIds.end(), entityConfiguration->getID()) == targetEntityIds.end())
                {
                    m_speedAltitudeVsEligibleEntityIds[std::make_pair(nominalSpeedToOneDecimalPlace_mps, nominalAltitudeRounded)].push_back(entityConfiguration->getID());
                }
            }
        }
        else if (dynamic_cast<afrl::cmasi::EntityState*> (object))
        {
            std::shared_ptr<afrl::cmasi::EntityState> entityState;
            entityState.reset(static_cast<afrl::cmasi::EntityState*> (object->clone()));
            m_entityStates[entityState->getID()] = entityState;
        }
        else if (afrl::cmasi::isMissionCommand(object))
        {
            std::shared_ptr<afrl::cmasi::MissionCommand> missionCommand;
            missionCommand.reset(static_cast<afrl::cmasi::MissionCommand*> (object->clone()));
            m_currentMissions[missionCommand->getVehicleID()] = missionCommand;
        }
        else if (afrl::impact::isAreaOfInterest(object))
        {
            std::shared_ptr<afrl::impact::AreaOfInterest> areaOfInterest;
            areaOfInterest.reset(static_cast<afrl::impact::AreaOfInterest*> (object->clone()));
            m_areasOfInterest[areaOfInterest->getAreaID()] = areaOfInterest;
        }
        else if (afrl::impact::isLineOfInterest(object))
        {
            std::shared_ptr<afrl::impact::LineOfInterest> lineOfInterest;
            lineOfInterest.reset(static_cast<afrl::impact::LineOfInterest*> (object->clone()));
            m_linesOfInterest[lineOfInterest->getLineID()] = lineOfInterest;
        }
        else if (afrl::impact::isPointOfInterest(object))
        {
            std::shared_ptr<afrl::impact::PointOfInterest> pointOfInterest;
            pointOfInterest.reset(static_cast<afrl::impact::PointOfInterest*> (object->clone()));
            m_pointsOfInterest[pointOfInterest->getPointID()] = pointOfInterest;
        }
        else if (afrl::cmasi::isKeepInZone(object))
        {
            std::shared_ptr<afrl::cmasi::KeepInZone> kiz;
            kiz.reset(static_cast<afrl::cmasi::KeepInZone*>(object->clone()));
            m_keepInZones[kiz->getZoneID()] = kiz;
        }
        else if (afrl::cmasi::isKeepOutZone(object))
        {
            std::shared_ptr<afrl::cmasi::KeepOutZone> koz;
            koz.reset(static_cast<afrl::cmasi::KeepOutZone*>(object->clone()));
            m_keepOutZones[koz->getZoneID()] = koz;
        }
        else if (afrl::cmasi::isOperatingRegion(object))
        {
            std::shared_ptr<afrl::cmasi::OperatingRegion> opr;
            opr.reset(static_cast<afrl::cmasi::OperatingRegion*>(object->clone()));
            m_OperatingRegions[opr->getID()] = opr;
        }
        delete object;
    }

    // set a (likely) unique ID from the task ID
    m_uniqueRouteRequestId = (rand() << 16) + m_task->getTaskID();
    if (m_uniqueRouteRequestId < 0)
        m_uniqueRouteRequestId = -m_uniqueRouteRequestId;

    //ENTITY CONFIGURATIONS
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
    for (auto child : childconfigs)
        addSubscriptionAddress(child);

    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for (auto child : childstates)
        addSubscriptionAddress(child);

    addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::UniqueAutomationResponse::Subscription);
    addSubscriptionAddress(uxas::messages::route::RoutePlanResponse::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskImplementationRequest::Subscription);

    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);

    isSuccessful = isSuccessful && configureTask(serviceXmlNode);

    return (isSuccessful);
};

bool TaskServiceBase::initialize()
{
    bool isSuccessful(true);
    isSuccessful = isSuccessful && initializeTask();
    return (isSuccessful);
};

bool TaskServiceBase::start()
{
    bool isSuccessful{true};
    isSuccessful = isSuccessful && startTask();
    if (isSuccessful)
    {
        auto taskStarted = std::make_shared<uxas::messages::task::TaskInitialized>();
        taskStarted->setTaskID(m_task->getTaskID());
        sendSharedLmcpObjectBroadcastMessage(taskStarted);
    }
    return (isSuccessful);
};

bool TaskServiceBase::terminate()
{
    bool isKillTheService(true);
    isKillTheService = terminateTask();
    return (isKillTheService);
};

bool TaskServiceBase::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    bool isKillService = false;

    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
    auto entityConfiguration = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);

    if (entityState)
    {
        m_entityStates[entityState->getID()] = entityState;
        if (m_assignedVehicleIds.find(entityState->getID()) != m_assignedVehicleIds.end())
        {
            bool isOnTask = std::find(entityState->getAssociatedTasks().begin(),
                    entityState->getAssociatedTasks().end(),
                    m_task->getTaskID()) != entityState->getAssociatedTasks().end();
            if (isOnTask)
            {
                activeEntityState(entityState); //virtual
                if (m_activeEntities.find(entityState->getID()) == m_activeEntities.end())
                {
                    // task just became active for this vehicle
                    m_activeEntities.insert(entityState->getID());
                    // send TaskActive message
                    std::this_thread::sleep_for(std::chrono::milliseconds(50));
                    COUT_INFO_MSG("Sending TaskActive !!!!")
                            auto taskActive = std::make_shared<uxas::messages::task::TaskActive>();
                    taskActive->setTaskID(m_task->getTaskID());
                    taskActive->setEntityID(entityState->getID());
                    taskActive->setTimeTaskActivated(uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms());
                    auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(taskActive);
                    sendSharedLmcpObjectBroadcastMessage(newMessage);
                    std::this_thread::sleep_for(std::chrono::milliseconds(50));
                }
                m_assignedVehicleIdVsLastTaskWaypoint[entityState->getID()] = entityState->getCurrentWaypoint();
                //COUT_INFO_MSG("entityState->getID()[" << entityState->getID() << "] entityState->getCurrentWaypoint()[" << entityState->getCurrentWaypoint() << "]")
            }
            else
            {
                if (m_activeEntities.find(entityState->getID()) != m_activeEntities.end())
                {
                    taskComplete(); // allow task to perform functions required at taskcomplete
                    // was active last state update, send taskcomplete message for this vehicle
                    m_activeEntities.erase(entityState->getID());
                    COUT_INFO_MSG("Sending TaskComplete !!!!")
                            // send out task complete - uxas
                            auto taskCompleteUxas = std::make_shared<uxas::messages::task::TaskComplete>();
                    for (auto& assignedVehicleId : m_assignedVehicleIds)
                    {
                        taskCompleteUxas->getEntitiesInvolved().push_back(assignedVehicleId);
                    }
                    taskCompleteUxas->setTaskID(m_task->getTaskID());
                    taskCompleteUxas->setTimeTaskCompleted(uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms());
                    auto newMessageUxas = std::static_pointer_cast<avtas::lmcp::Object>(taskCompleteUxas);
                    sendSharedLmcpObjectBroadcastMessage(newMessageUxas);
                    m_assignedVehicleIdVsLastTaskWaypoint.erase(entityState->getID());
                }
            }
        }
    }
    else if (entityConfiguration)
    {
        auto foundEntity = std::find(m_task->getEligibleEntities().begin(), m_task->getEligibleEntities().end(), entityConfiguration->getID());
        if (m_task->getEligibleEntities().empty() || foundEntity != m_task->getEligibleEntities().end())
        {
            m_entityConfigurations.insert(std::make_pair(entityConfiguration->getID(), entityConfiguration));
            auto nominalSpeedToOneDecimalPlace_mps = std::round(entityConfiguration->getNominalSpeed()*10.0) / 10.0;
            auto nominalAltitudeRounded = std::round(entityConfiguration->getNominalAltitude());
            auto targetEntityIds = m_speedAltitudeVsEligibleEntityIds[std::make_pair(nominalSpeedToOneDecimalPlace_mps, nominalAltitudeRounded)];
            if (std::find(targetEntityIds.begin(), targetEntityIds.end(), entityConfiguration->getID()) == targetEntityIds.end())
            {
                m_speedAltitudeVsEligibleEntityIds[std::make_pair(nominalSpeedToOneDecimalPlace_mps, nominalAltitudeRounded)].push_back(entityConfiguration->getID());
            }
        }
    }
    else if (uxas::messages::task::isUniqueAutomationRequest(receivedLmcpMessage->m_object))
    {
        auto uniqueAutomationRequest = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage->m_object);
        //COUT_FILE_LINE_MSG("uniqueAutomationRequest->getRequestID()[" << uniqueAutomationRequest->getRequestID() << "]")
        if (m_task && uniqueAutomationRequest)
        {
            //COUT_FILE_LINE_MSG("uniqueAutomationRequest->getRequestID()[" << uniqueAutomationRequest->getRequestID() << "]")
            m_latestUniqueAutomationRequestId = uniqueAutomationRequest->getRequestID();
            m_idVsUniqueAutomationRequest[uniqueAutomationRequest->getRequestID()] = uniqueAutomationRequest;
            if (std::find(uniqueAutomationRequest->getOriginalRequest()->getTaskList().begin(),
                    uniqueAutomationRequest->getOriginalRequest()->getTaskList().end(),
                    m_task->getTaskID()) != uniqueAutomationRequest->getOriginalRequest()->getTaskList().end())
            {
                //planner should restart any tasks that have been performed or are currently being performed
                int64_t vehicleIdRestart{-1};
                int64_t waypointIdRestart{-1};
                int64_t optionIdRestart{-1};
                if ((!uniqueAutomationRequest->getOriginalRequest()->getRedoAllTasks()) && (!m_assignedVehicleIdVsLastTaskWaypoint.empty()))
                {
                    for (auto& assignedVehicleIdAndLastTaskWaypoint : m_assignedVehicleIdVsLastTaskWaypoint)
                    {
                        //COUT_FILE_LINE_MSG("vehicleIdRestart[" << assignedVehicleIdAndLastTaskWaypoint.first
                        //        << "] waypointIdRestart[" << assignedVehicleIdAndLastTaskWaypoint.second << "]")
                        if (std::find(uniqueAutomationRequest->getOriginalRequest()->getEntityList().begin(),
                                uniqueAutomationRequest->getOriginalRequest()->getEntityList().end(),
                                assignedVehicleIdAndLastTaskWaypoint.first) !=
                                uniqueAutomationRequest->getOriginalRequest()->getEntityList().end())
                        {
                            vehicleIdRestart = assignedVehicleIdAndLastTaskWaypoint.first;
                            waypointIdRestart = assignedVehicleIdAndLastTaskWaypoint.second;
                            //COUT_FILE_LINE_MSG("vehicleIdRestart[" << vehicleIdRestart << "] waypointIdRestart[" << waypointIdRestart << "]")
                            if (m_assignedVehicleIdVsAssignedOptionId.find(vehicleIdRestart) != m_assignedVehicleIdVsAssignedOptionId.end())
                            {
                                optionIdRestart = m_assignedVehicleIdVsAssignedOptionId[vehicleIdRestart];
                                //COUT_FILE_LINE_MSG("vehicleIdRestart[" << vehicleIdRestart << "] optionIdRestart[" << optionIdRestart << "]")
                            }
                            // assume we are only restarting task on one vehicle
                            break;
                        }
                    }
                }

                auto itOption = m_optionIdVsTaskOptionClass.find(optionIdRestart);
                if ((vehicleIdRestart > 0) && itOption != m_optionIdVsTaskOptionClass.end())
                {
                    if (waypointIdRestart < itOption->second->m_firstTaskActiveWaypointID)
                    {
                        // only restart if vehicle was operating on active waypoints
                        vehicleIdRestart = -1;
                        waypointIdRestart = -1;
                        optionIdRestart = -1;
                    }
                }
                else
                {
                    vehicleIdRestart = -1;
                    waypointIdRestart = -1;
                    optionIdRestart = -1;
                }

                if ((vehicleIdRestart > 0) && (optionIdRestart > 0) && itOption->second && itOption->second->m_taskOption)
                {
                    // restart plan where the restart vehicle left it
                    // create new option with only the restart vehicle eligible
                    m_taskPlanOptions = std::make_shared<uxas::messages::task::TaskPlanOptions>();
                    m_taskPlanOptions->setCorrespondingAutomationRequestID(uniqueAutomationRequest->getRequestID());
                    m_taskPlanOptions->setTaskID(m_task->getTaskID());

                    itOption->second->m_restartTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(itOption->second->m_taskOption->clone());
                    itOption->second->m_restartTaskOption->getEligibleEntities().clear();
                    itOption->second->m_restartTaskOption->getEligibleEntities().push_back(vehicleIdRestart);

                    // Build the Restart Task 

                    double distance_m = 0.0;
                    double startHeading_deg = 0.0;
                    double endHeading_deg = 0.0;
                    afrl::cmasi::Waypoint * lastWaypoint{nullptr};
                    Dpss_Data_n::xyPoint lastVehiclePosition;
                    Dpss_Data_n::xyPoint currentVehiclePosition;
                    Dpss_Data_n::xyPoint lastlastVehiclePosition; // used to calculate end heading

                    uxas::common::utilities::CUnitConversions unitConversions;

                    // find the waypoints from (restartId - 1) to the end of the plan
                    itOption->second->m_restartRoutePlan = std::make_shared<uxas::messages::route::RoutePlan>();
                    itOption->second->m_restartRoutePlan->setRouteID(TaskOptionClass::m_firstImplementationRouteId);
                    auto itRoute = itOption->second->m_orderedRouteIdVsPlan.find(TaskOptionClass::m_firstImplementationRouteId);
                    if (itRoute != itOption->second->m_orderedRouteIdVsPlan.end())
                    {
                        for (auto& planWaypoint : itRoute->second->getWaypoints())
                        {
                            //COUT_INFO_MSG("waypointIdRestart[" << waypointIdRestart << "], planWaypoint->getNumber()[" << planWaypoint->getNumber() << "]")
                            if ((waypointIdRestart == planWaypoint->getNumber()) && lastWaypoint) // found one waypoint past start of the restart plan
                            {
                                //COUT_INFO_MSG("waypointIdRestart[" << waypointIdRestart << "], planWaypoint->getNumber()[" << planWaypoint->getNumber() << "]")
                                itOption->second->m_restartRoutePlan->getWaypoints().push_back(lastWaypoint->clone());
                                // calculate xy coordinates for last waypoint
                                double north_m(0.0);
                                double east_m(0.0);
                                unitConversions.ConvertLatLong_degToNorthEast_m(planWaypoint->getLatitude(),
                                        planWaypoint->getLongitude(), north_m, east_m);

                                currentVehiclePosition.x = north_m;
                                currentVehiclePosition.y = east_m;
                            }
                            if (!itOption->second->m_restartRoutePlan->getWaypoints().empty()) // we have found the plan
                            {
                                //COUT_INFO_MSG("waypointIdRestart[" << waypointIdRestart << "], planWaypoint->getNumber()[" << planWaypoint->getNumber() << "]")
                                itOption->second->m_restartRoutePlan->getWaypoints().push_back(planWaypoint->clone());

                                double north_m(0.0);
                                double east_m(0.0);
                                unitConversions.ConvertLatLong_degToNorthEast_m(planWaypoint->getLatitude(),
                                        planWaypoint->getLongitude(), north_m, east_m);
                                Dpss_Data_n::xyPoint currentVehiclePosition(north_m, east_m, 0.0);

                                distance_m += currentVehiclePosition.dist(lastVehiclePosition);

                                if (itOption->second->m_restartRoutePlan->getWaypoints().size() == 2)
                                {
                                    //TODO:: need to check this!!!!!!
                                    startHeading_deg = lastVehiclePosition.heading2d(currentVehiclePosition);
                                }

                            }
                            lastWaypoint = planWaypoint; //DON'T OWN THIS POINTER!!!!
                            lastlastVehiclePosition = lastVehiclePosition;
                            lastVehiclePosition = currentVehiclePosition;
                        }
                    }
                    lastWaypoint = nullptr; // finished with this, we don't own it

                    //TODO:: need to check this!!!!!!
                    endHeading_deg = lastlastVehiclePosition.heading2d(lastVehiclePosition);

                    //TODO:: calculate cost, need vehicle speed
                    double vehicleSpeed_ms{0.0};

                    if (m_entityConfigurations.find(vehicleIdRestart) != m_entityConfigurations.end())
                    {
                        vehicleSpeed_ms = m_entityConfigurations[vehicleIdRestart]->getNominalSpeed();
                    }

                    int64_t cost_ms = INT64_MAX;
                    if (vehicleSpeed_ms > 0.0)
                    {
                        cost_ms = static_cast<int64_t> (static_cast<double> (distance_m) / vehicleSpeed_ms * 1000.0);
                    }
                    else
                    {
                        //TODO ERROR:: could not find vehicle configuration or vehicleSpeed_ms <= 0.0
                    }

                    if (!(itOption->second->m_restartRoutePlan->getWaypoints().empty()))
                    {
                        itOption->second->m_restartTaskOption->setCost(cost_ms);
                        itOption->second->m_restartTaskOption->setStartLocation(itOption->second->m_restartRoutePlan->getWaypoints().front()->clone());
                        itOption->second->m_restartTaskOption->setStartHeading(startHeading_deg);
                        itOption->second->m_restartTaskOption->setEndLocation(itOption->second->m_restartRoutePlan->getWaypoints().back()->clone());
                        itOption->second->m_restartTaskOption->setEndHeading(endHeading_deg);
                        m_taskPlanOptions->getOptions().push_back(itOption->second->m_restartTaskOption->clone());

                        std::string compositionString("+(");
                        compositionString += "p";
                        compositionString += std::to_string(optionIdRestart);
                        compositionString += " ";
                        compositionString += ")";

                        m_taskPlanOptions->setComposition(compositionString);
                        auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
                        sendSharedLmcpObjectBroadcastMessage(newResponse);
                    }
                    else
                    {
                        // TODO ERROR: calculated that a restart route was in place, but no waypoints in plan
                    }
                }
                else
                {
                    m_pendingImplementationRouteRequests.clear();
                    // select requested eligible entities, defaults to use them all
                    m_speedAltitudeVsEligibleEntityIdsRequested.clear();
                    if (!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())
                    {
                        for (auto itEligibleEntities = m_speedAltitudeVsEligibleEntityIds.begin();
                                itEligibleEntities != m_speedAltitudeVsEligibleEntityIds.end();
                                itEligibleEntities++)
                        {
                            for (auto& eligibleEntity : itEligibleEntities->second)
                            {
                                if (std::find(uniqueAutomationRequest->getOriginalRequest()->getEntityList().begin(),
                                        uniqueAutomationRequest->getOriginalRequest()->getEntityList().end(),
                                        eligibleEntity) !=
                                        uniqueAutomationRequest->getOriginalRequest()->getEntityList().end())
                                {
                                    m_speedAltitudeVsEligibleEntityIdsRequested[itEligibleEntities->first].push_back(eligibleEntity);
                                }
                            }
                        }
                    }
                    else
                    {
                        m_speedAltitudeVsEligibleEntityIdsRequested = m_speedAltitudeVsEligibleEntityIds;
                    }
                    // set/reset task plan options               
                    m_taskPlanOptions = std::make_shared<uxas::messages::task::TaskPlanOptions>();
                    m_taskPlanOptions->setCorrespondingAutomationRequestID(uniqueAutomationRequest->getRequestID());
                    m_taskPlanOptions->setTaskID(m_task->getTaskID());
                    m_optionIdVsTaskOptionClass.clear();
                    m_routeIdVsTaskImplementationRequest.clear();
                    m_pendingOptionRouteRequests.clear();
                    m_pendingImplementationRouteRequests.clear();

                    //build and send out a 'TaskPlanOptions' message
                    buildTaskPlanOptions();
                }
            }
        }
        else
        {
            if (!uniqueAutomationRequest)
            {
                //TODO:: error unable to decode UniqueAutomationRequest
                CERR_FILE_LINE_MSG("Task [" << m_task->getTaskID()<< "] unable to interpret request")
            }
            if (!m_task)
            {
                //TODO:: error invalid task object encountered when receiving a UniqueAutomationRequest
            }
        }
        //COUT_INFO_MSG("")
    }
    else if (uxas::messages::task::isUniqueAutomationResponse(receivedLmcpMessage->m_object))
    {
        // UniqueAutomationResponse(s) to determine which vehicles are assigned to this task 
        auto uniqueAutomationResponse = std::static_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(receivedLmcpMessage->m_object);

        if (m_idVsUniqueAutomationRequest.find(uniqueAutomationResponse->getResponseID()) == m_idVsUniqueAutomationRequest.end())
        {
            //TODO:: "warning received uniqueAutomationResponse[",uniqueAutomationResponse->getResponseID(),"] with no corresponding uniqueAutomationRequest"
        }
        else
        {
            auto currentAutomationRequest = m_idVsUniqueAutomationRequest[uniqueAutomationResponse->getResponseID()];

            //TODO:: change to look up uniqueautomationrequest and delete it when finished
            if (!currentAutomationRequest->getSandBoxRequest())
            {
                // remove any assigned entities that appear in the uniqueAutomationResponse.
                // Note: if an entity has been reassigned, then it will be added back below
                for (auto& missionCommand : uniqueAutomationResponse->getOriginalResponse()->getMissionCommandList())
                {
                    m_assignedVehicleIds.erase(missionCommand->getVehicleID());
                    m_activeEntities.erase(missionCommand->getVehicleID());
                }
                // search through the waypoints to find vehicles that have been assigned
                for (auto& missionCommand : uniqueAutomationResponse->getOriginalResponse()->getMissionCommandList())
                {
                    for (auto& waypoint : missionCommand->getWaypointList())
                    {
                        bool isOnTask = std::find(waypoint->getAssociatedTasks().begin(),
                                waypoint->getAssociatedTasks().end(),
                                m_task->getTaskID()) != waypoint->getAssociatedTasks().end();
                        if (isOnTask)
                        {
                            m_assignedVehicleIds.insert(missionCommand->getVehicleID());
                        }
                    }
                }
            }
            m_idVsUniqueAutomationRequest.erase(uniqueAutomationResponse->getResponseID());
        }
    }
    else if (uxas::messages::task::isTaskImplementationRequest(receivedLmcpMessage->m_object))
    {
        if (m_task)
        {
            auto taskImplementationRequest = std::static_pointer_cast<uxas::messages::task::TaskImplementationRequest>(receivedLmcpMessage->m_object);
            if (taskImplementationRequest->getTaskID() == m_task->getTaskID())
            {
                auto itOption = m_optionIdVsTaskOptionClass.find(taskImplementationRequest->getOptionID());
                if (itOption != m_optionIdVsTaskOptionClass.end())
                {
                    buildAndSendImplementationRouteRequestBase(taskImplementationRequest->getOptionID(),
                            taskImplementationRequest, itOption->second->m_taskOption);
                }
                else
                {
                    CERR_FILE_LINE_MSG("ERROR::TaskServiceBase::ProcessMessage: for TaskId[" << m_task->getTaskID()
                            << "] OptionId[" << taskImplementationRequest->getOptionID()
                            << "] does not exist, but was specified in a TaskImplementationRequest.")
                }
            }
        } //if(m_pointSearchTask)
    }
    else if (uxas::messages::route::isRoutePlanResponse(receivedLmcpMessage->m_object))
    {
        auto routePlanResponse = std::static_pointer_cast<uxas::messages::route::RoutePlanResponse>(receivedLmcpMessage->m_object);
        if (routePlanResponse->getAssociatedTaskID() == m_task->getTaskID())
        {
            auto routeType = getRouteTypeFromRouteId(routePlanResponse->getResponseID());
            switch (routeType)
            {
                default:
                    CERR_FILE_LINE_MSG("ERROR::isProcessedMessageBase:: unknown RoutePlanResponseEncountered for  ResponseID[" << routePlanResponse->getResponseID() << "]")
                    break;
                case RouteTypeEnum::OPTION:
                    processOptionsRoutePlanResponseBase(routePlanResponse);
                    break;
                case RouteTypeEnum::IMPLEMENTATION:
                    processImplementationRoutePlanResponseBase(routePlanResponse);
                    break;
            }
        }
    }
    else if (afrl::cmasi::isAutomationResponse(receivedLmcpMessage->m_object))
    {
        auto ares = std::static_pointer_cast<afrl::cmasi::AutomationResponse>(receivedLmcpMessage->m_object);
        for (auto v : ares->getMissionCommandList())
        {
            m_currentMissions[v->getVehicleID()] = std::shared_ptr<afrl::cmasi::MissionCommand>(v->clone());
        }
    }
    else if (afrl::cmasi::isMissionCommand(receivedLmcpMessage->m_object))
    {
        auto mish = std::static_pointer_cast<afrl::cmasi::MissionCommand>(receivedLmcpMessage->m_object);
        m_currentMissions[mish->getVehicleID()] = mish;
    }

    isKillService = isKillService || processReceivedLmcpMessageTask(receivedLmcpMessage->m_object);

    return (isKillService);
};

int64_t TaskServiceBase::getOptionRouteId(const int64_t& OptionId)
{
    m_routeType[m_uniqueRouteRequestId] = RouteTypeEnum::OPTION;
    m_routeOption[m_uniqueRouteRequestId] = OptionId;
    return m_uniqueRouteRequestId++; // post increment
}

int64_t TaskServiceBase::getImplementationRouteId(const int64_t& OptionId)
{
    m_routeType[m_uniqueRouteRequestId] = RouteTypeEnum::IMPLEMENTATION;
    m_routeOption[m_uniqueRouteRequestId] = OptionId;
    return m_uniqueRouteRequestId++; // post increment
}

int64_t TaskServiceBase::getOptionIdFromRouteId(const int64_t& routeId)
{
    auto findID = m_routeOption.find(routeId);
    if (findID != m_routeOption.end())
    {
        return m_routeOption[routeId];
    }
    return 0;
}

TaskServiceBase::RouteTypeEnum TaskServiceBase::getRouteTypeFromRouteId(const int64_t& routeId)
{
    auto findID = m_routeType.find(routeId);
    if (findID != m_routeType.end())
    {
        return m_routeType[routeId];
    }
    return RouteTypeEnum::UNKNOWN;
}

void TaskServiceBase::buildAndSendImplementationRouteRequestBase(const int64_t& optionId,
        const std::shared_ptr<uxas::messages::task::TaskImplementationRequest>& taskImplementationRequest,
        const std::shared_ptr<uxas::messages::task::TaskOption>& taskOption)
{
    // check to see is there is a virtual class handler
    if (!isBuildAndSendImplementationRouteRequest(optionId, taskImplementationRequest, taskOption))
    {
        auto itTaskOptionClass = m_optionIdVsTaskOptionClass.find(optionId);
        if (itTaskOptionClass != m_optionIdVsTaskOptionClass.end())
        {
            auto routePlanRequest = std::make_shared<uxas::messages::route::RoutePlanRequest>();
            routePlanRequest->setRequestID(getImplementationRouteId(optionId));
            routePlanRequest->setAssociatedTaskID(m_task->getTaskID());
            routePlanRequest->setIsCostOnlyRequest(false);
            routePlanRequest->setOperatingRegion(taskImplementationRequest->getRegionID());
            routePlanRequest->setVehicleID(taskImplementationRequest->getVehicleID());
            m_pendingImplementationRouteRequests.insert(routePlanRequest->getRequestID());

            auto routeConstraints = new uxas::messages::route::RouteConstraints();
            int64_t routeId = itTaskOptionClass->second->m_routeIdFromLastTask;
            m_transitionRouteRequestId = routeId;
            itTaskOptionClass->second->m_pendingRouteIds.insert(routeId);
            routeConstraints->setRouteID(routeId);
            routeConstraints->setStartLocation(taskImplementationRequest->getStartPosition()->clone());
            routeConstraints->setStartHeading(taskImplementationRequest->getStartHeading());

            if (itTaskOptionClass->second->m_restartRoutePlan)
            {
                if (itTaskOptionClass->second->m_restartTaskOption)
                {
                    routeConstraints->setEndLocation(itTaskOptionClass->second->m_restartTaskOption->getStartLocation()->clone());
                    routeConstraints->setEndHeading(itTaskOptionClass->second->m_restartTaskOption->getStartHeading());
                }
                else
                {
                    CERR_FILE_LINE_MSG("ERROR::buildAndSendImplementationRouteRequestBase:: m_restartTaskOption not set! ")
                }
            }
            else
            {
                routeConstraints->setEndLocation(taskOption->getStartLocation()->clone());
                routeConstraints->setEndHeading(taskOption->getStartHeading());
            }

            if (itTaskOptionClass->second->m_routePlanRequest)
            {
                routeId = itTaskOptionClass->second->m_firstImplementationRouteId;
                for (auto& routeConstraints : itTaskOptionClass->second->m_routePlanRequest->getRouteRequests())
                {
                    routePlanRequest->getRouteRequests().push_back(routeConstraints->clone());
                    routePlanRequest->getRouteRequests().back()->setRouteID(routeId);
                    itTaskOptionClass->second->m_pendingRouteIds.insert(routeId);
                    routeId++;
                }
            }

            routePlanRequest->getRouteRequests().push_back(routeConstraints);
            routeConstraints = nullptr; //just gave up ownership

            m_routeIdVsTaskImplementationRequest[routePlanRequest->getRequestID()] = taskImplementationRequest;

            auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(routePlanRequest);
            sendSharedLmcpObjectBroadcastMessage(newMessage);
        }
        else //if ((itTaskOptionClass != m_optionIdVsTaskOptionClass.end()))
        {
            CERR_FILE_LINE_MSG("ERROR::buildAndSendImplementationRouteRequestBase:: TaskOptionClass not found for optionId[" << optionId << "]")
        }
    }
}

void TaskServiceBase::processOptionsRoutePlanResponseBase(const std::shared_ptr<uxas::messages::route::RoutePlanResponse>& routePlanResponse)
{
    auto itResponseId = m_pendingOptionRouteRequests.find(routePlanResponse->getResponseID());
    if (itResponseId != m_pendingOptionRouteRequests.end())
    {
        m_pendingOptionRouteRequests.erase(routePlanResponse->getResponseID());
        auto optionId = getOptionIdFromRouteId(routePlanResponse->getResponseID());
        auto vehicleId = routePlanResponse->getVehicleID();
        auto operatingRegion = routePlanResponse->getOperatingRegion();
        auto itTaskOptionClass = m_optionIdVsTaskOptionClass.find(optionId);
        if (itTaskOptionClass != m_optionIdVsTaskOptionClass.end())
        {
            for (auto routePlan : routePlanResponse->getRouteResponses())
            {
                // we are waiting for this one
                auto route = std::shared_ptr<uxas::messages::route::RoutePlan>(routePlan->clone());
                // call virtual function
                if (!isHandleOptionsRouteResponse(vehicleId, optionId, operatingRegion, route))
                {
                    if (itTaskOptionClass->second->m_pendingRouteIds.find(route->getRouteID()) != itTaskOptionClass->second->m_pendingRouteIds.end())
                    {
                        // remove the route from the pending list
                        itTaskOptionClass->second->m_pendingRouteIds.erase(route->getRouteID());
                        // add this route's cost to the total for this option
                        auto totalCost = MAX_TOTAL_COST_MS;
                        if (route->getRouteCost() > 0)
                        {
                            totalCost = itTaskOptionClass->second->m_taskOption->getCost() + route->getRouteCost();
                        }
                        itTaskOptionClass->second->m_taskOption->setCost(totalCost);
                        if (itTaskOptionClass->second->m_pendingRouteIds.empty())
                        {
                            // once this option is complete, add to the options and remove it from the list
                            m_taskPlanOptions->getOptions().push_back(itTaskOptionClass->second->m_taskOption->clone());
                        }
                    }
                    bool isAllOptionsComplete = true;
                    for (auto& taskOptionClass : m_optionIdVsTaskOptionClass)
                    {
                        if (!taskOptionClass.second->m_pendingRouteIds.empty())
                        {
                            isAllOptionsComplete = false;
                            break;
                        }
                    }
                    if (isAllOptionsComplete)
                    {
                        // once all options are complete, send out the message
                        auto objectTaskPlanOptions = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
                        sendSharedLmcpObjectBroadcastMessage(objectTaskPlanOptions);
                    }
                }
            } //for (auto routePlan : routePlanResponse->getRouteResponses())
        }
        else //if (itTaskOptionClass != m_optionIdVsTaskOptionClass.end())
        {
            CERR_FILE_LINE_MSG("ERROR::processOptionsRouteResponse:: TaskOptionClass not found for optionId[" << optionId << "]")
        }
    }
    else //if (itResponseId != m_pendingOptionRouteRequests.end())
    {
        CERR_FILE_LINE_MSG("ERROR::processOptionsRoutePlanResponseBase:: RoutePlanResponse received that was not expected, RoutePlanId[" << routePlanResponse->getResponseID() << "]")
    }
}

void TaskServiceBase::processImplementationRoutePlanResponseBase(const std::shared_ptr<uxas::messages::route::RoutePlanResponse>& routePlanResponse)
{
    if (m_idVsUniqueAutomationRequest.find(m_latestUniqueAutomationRequestId) == m_idVsUniqueAutomationRequest.end())
    {
        //TODO:: "warning received uniqueAutomationResponse[",m_latestUniqueAutomationRequestId,"] with no corresponding uniqueAutomationRequest"
    }
    else
    {
        auto currentAutomationRequest = m_idVsUniqueAutomationRequest[m_latestUniqueAutomationRequestId];

        auto itPlanResponseId = m_pendingImplementationRouteRequests.find(routePlanResponse->getResponseID());
        if (itPlanResponseId != m_pendingImplementationRouteRequests.end())
        {
            m_pendingImplementationRouteRequests.erase(routePlanResponse->getResponseID());

            auto optionId = getOptionIdFromRouteId(routePlanResponse->getResponseID());
            auto vehicleId = routePlanResponse->getVehicleID();
            auto itTaskOptionClass = m_optionIdVsTaskOptionClass.find(optionId);
            auto itTaskImplementationRequest = m_routeIdVsTaskImplementationRequest.find(routePlanResponse->getResponseID());
            if ((itTaskOptionClass != m_optionIdVsTaskOptionClass.end()) &&
                    (itTaskImplementationRequest != m_routeIdVsTaskImplementationRequest.end()))
            {
                itTaskOptionClass->second->m_firstTaskActiveWaypointID = -1;
                for (auto routePlan : routePlanResponse->getRouteResponses())
                {
                    if (itTaskOptionClass->second->m_pendingRouteIds.find(routePlan->getRouteID()) != itTaskOptionClass->second->m_pendingRouteIds.end())
                    {
                        // remove the routePlan from the pending list
                        itTaskOptionClass->second->m_pendingRouteIds.erase(routePlan->getRouteID());
                        // add this routePlan's cost to the total for this option
                        auto totalCost = itTaskOptionClass->second->m_taskOption->getCost();
                        if (routePlan->getRouteID() == m_transitionRouteRequestId)
                        {
                            if (routePlan->getRouteCost() > 0)
                            {
                                totalCost += routePlan->getRouteCost();
                            }
                            else
                            {
                                // this is an error!!!!
                                totalCost = MAX_TOTAL_COST_MS;
                            }
                            // update total task cost to include en-route time
                            itTaskOptionClass->second->m_taskOption->setCost(totalCost);
                        }
                        /////////////////////////////////////////////////////////////////////////////////////////////////////
                        auto pRoutePlan = std::shared_ptr<uxas::messages::route::RoutePlan>(routePlan->clone());
                        itTaskOptionClass->second->m_orderedRouteIdVsPlan[routePlan->getRouteID()] = pRoutePlan;
                        // once all of the routePlans have been received, build the response and send it out
                        if (itTaskOptionClass->second->m_pendingRouteIds.empty())
                        {
                            auto itEntityConfiguration = m_entityConfigurations.find(vehicleId);
                            if (itEntityConfiguration != m_entityConfigurations.end())
                            {
                                // build a TaskImplementationResponse
                                auto taskImplementationResponse = std::make_shared<uxas::messages::task::TaskImplementationResponse>();
                                taskImplementationResponse->setResponseID(itTaskImplementationRequest->second->getRequestID());
                                taskImplementationResponse->setCorrespondingAutomationRequestID(itTaskImplementationRequest->second->getCorrespondingAutomationRequestID());
                                taskImplementationResponse->setTaskID(m_task->getTaskID());
                                taskImplementationResponse->setOptionID(optionId);
                                taskImplementationResponse->setVehicleID(vehicleId);
                                taskImplementationResponse->setFinalLocation(itTaskOptionClass->second->m_taskOption->getEndLocation()->clone());
                                taskImplementationResponse->setFinalHeading(itTaskOptionClass->second->m_taskOption->getEndHeading());
                                taskImplementationResponse->setFinalTime(itTaskImplementationRequest->second->getStartTime() + itTaskOptionClass->second->m_taskOption->getCost());
                                int64_t waypointId = itTaskImplementationRequest->second->getStartingWaypointID();
                                m_optionWaypointIdVsFinalWaypointId.clear();
                                // waypoints from the saved routes
                                bool isFirstWaypoint = true;
                                bool isFoundTaskWaypoints = false;
                                for (auto& plan : itTaskOptionClass->second->m_orderedRouteIdVsPlan)
                                {
                                    bool isRouteFromLastToTask = (plan.second->getRouteID() == m_transitionRouteRequestId);
                                    auto taskPlan = plan.second;
                                    if (!isRouteFromLastToTask)
                                    {
                                        if (itTaskOptionClass->second->m_restartRoutePlan)
                                        {
                                            if (!isFoundTaskWaypoints) // only add the restartRoutePlan, don't add any other routes
                                            {
                                                taskPlan = itTaskOptionClass->second->m_restartRoutePlan;
                                            }
                                            else
                                            {
                                                // already added the restart waypoints, don't add anymore
                                                taskPlan = std::make_shared<uxas::messages::route::RoutePlan>();
                                            }
                                            isFoundTaskWaypoints = true;
                                        }
                                    }
                                    for (auto& planWaypoint : taskPlan->getWaypoints())
                                    {
                                        auto originalPlanWaypointNumber = planWaypoint->getNumber();
                                        auto waypoint = planWaypoint->clone();
                                        planWaypoint->setNumber(waypointId); // need to update the number in the save route waypoints
                                        waypoint->setNumber(waypointId);
                                        waypoint->setAltitude(itEntityConfiguration->second->getNominalAltitude());
                                        waypoint->setAltitudeType(itEntityConfiguration->second->getNominalAltitudeType());
                                        waypoint->setSpeed(itEntityConfiguration->second->getNominalSpeed());
                                        if (!isFirstWaypoint)
                                        {
                                            //NOTE:: not setting nextwaypoint in saved plan, assume it is not needed and gets set here during implementation
                                            taskImplementationResponse->getTaskWaypoints().back()->setNextWaypoint(waypointId);
                                        }
                                        isFirstWaypoint = false;

                                        // add task active waypoints
                                        if ((!isRouteFromLastToTask || m_isMakeTransitionWaypointsActive))
                                        {
                                            if(!m_isMakeTransitionWaypointsActive)
                                            {
                                                m_optionWaypointIdVsFinalWaypointId[waypoint->getNumber()] = originalPlanWaypointNumber;
                                            }
                                            waypoint->getAssociatedTasks().push_back(m_task->getTaskID());
                                            if ((itTaskOptionClass->second->m_firstTaskActiveWaypointID < 0) && (!isRouteFromLastToTask) && (!currentAutomationRequest->getSandBoxRequest()))
                                            {
                                                itTaskOptionClass->second->m_firstTaskActiveWaypointID = waypointId;
                                            }
                                        }

                                        // if a waypoint is co-located with the previous waypoint, replace the previous waypoint
                                        if(!taskImplementationResponse->getTaskWaypoints().empty() &&
                                            isColocated(taskImplementationResponse->getTaskWaypoints().back(), waypoint))
                                        {
                                            waypointId = taskImplementationResponse->getTaskWaypoints().back()->getNumber();
                                            int64_t nextId = taskImplementationResponse->getTaskWaypoints().back()->getNextWaypoint();
                                            waypoint->setNumber(waypointId);
                                            waypoint->setNextWaypoint(nextId);
                                            delete taskImplementationResponse->getTaskWaypoints().back();
                                            taskImplementationResponse->getTaskWaypoints().pop_back();
                                        }

                                        taskImplementationResponse->getTaskWaypoints().push_back(waypoint);
                                        waypointId++;
                                        waypoint = nullptr; // gave up ownership
                                    }
                                }
                                // got a new plan so remove old restart plan, if any
                                itTaskOptionClass->second->m_restartRoutePlan.reset();
                                // TODO:: not sure what to do with the next section for task restart
                                isProcessTaskImplementationRouteResponse(taskImplementationResponse, itTaskOptionClass->second, waypointId, pRoutePlan);
                                if (!taskImplementationResponse->getTaskWaypoints().empty())
                                {
                                    if (taskImplementationResponse->getTaskWaypoints().back()->getAssociatedTasks().empty())
                                    {
                                        taskImplementationResponse->getTaskWaypoints().back()->getAssociatedTasks().push_back(m_task->getTaskID());
                                    }

                                    // disassociate the last waypoint in the plan from the tasks, allows tasks to complete
                                    if (taskImplementationResponse->getTaskWaypoints().back()->getNextWaypoint() == 0)
                                    {
                                        auto waypointLast = taskImplementationResponse->getTaskWaypoints().back()->clone();
                                        auto newNumber = waypointLast->getNumber() + 1;
                                        waypointLast->setNumber(newNumber);
                                        waypointLast->setNextWaypoint(newNumber);
                                        taskImplementationResponse->getTaskWaypoints().back()->setNextWaypoint(newNumber);
                                        waypointLast->getAssociatedTasks().clear();
                                        taskImplementationResponse->getTaskWaypoints().push_back(waypointLast);
                                        waypointLast = nullptr;
                                    }

                                    // send out the response
                                    auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(taskImplementationResponse);
                                    sendSharedLmcpObjectBroadcastMessage(newMessage);
                                    m_assignedVehicleIdVsAssignedOptionId[vehicleId] = optionId;
                                }
                                else //if(!taskImplementationResponse->getTaskWaypoints().empty())
                                {
                                    CERR_FILE_LINE_MSG("ERROR::TaskServiceBase::processRouteResponse: for TaskId[" << m_task->getTaskID()
                                            << "] OptionId[" << itTaskOptionClass->second->m_taskOption->getOptionID()
                                            << "], the plan waypoints are empty.")
                                } //if(!taskImplementationResponse->getTaskWaypoints().empty())
                                // done with this request
                                m_transitionRouteRequestId = 0;
                                //m_optionIdVsTaskOptionClass.clear();    // TODO:: should be able to reuse this for other requests
                            }
                            else //if (itEntityConfiguration != m_idVsEntityConfiguration.end())
                            {
                                // Assignment algorithm selected an invalid vehicle/option combination.
                                // This should never happen; fallback, send empty task implementation response
                                CERR_FILE_LINE_MSG("ERROR::c_Task_Base::isProcessedMessageBase: for TaskId[" << m_task->getTaskID()
                                        << "] there is not an EntityConfiguration for EntityId[" << vehicleId << "].")

                                        // send out the blank response
                                        auto taskImplementationResponse = std::make_shared<uxas::messages::task::TaskImplementationResponse>();
                                taskImplementationResponse->setResponseID(itTaskImplementationRequest->second->getRequestID());
                                taskImplementationResponse->setCorrespondingAutomationRequestID(itTaskImplementationRequest->second->getCorrespondingAutomationRequestID());
                                taskImplementationResponse->setTaskID(m_task->getTaskID());
                                taskImplementationResponse->setOptionID(optionId);
                                taskImplementationResponse->setVehicleID(vehicleId);
                                taskImplementationResponse->setFinalLocation(itTaskImplementationRequest->second->getStartPosition()->clone());
                                taskImplementationResponse->setFinalHeading(itTaskImplementationRequest->second->getStartHeading());
                                sendSharedLmcpObjectBroadcastMessage(taskImplementationResponse);
                            } //if (itEntityConfiguration != m_idVsEntityConfiguration.end())
                        } //if(itTaskOptionClass->second->m_pendingRouteIds.empty())
                    } //if(itTaskOptionClass->second->m_pendingRouteIds.find(routePlan->getRouteID()) != itTaskOptionClass->second->m_pendingRouteIds.end())
                } //for (auto& routePlan : routePlanResponse->getRouteResponses())
                m_routeIdVsTaskImplementationRequest.erase(routePlanResponse->getResponseID());
            }
            else //if(itTaskOptionClass != m_optionIdVsTaskOptionClass.end())
            {
                CERR_FILE_LINE_MSG("ERROR::processImplementationRouteResponseBase:: TaskOptionClass not found for optionId[" << optionId << "]")
            } //if(itTaskOptionClass != m_optionIdVsTaskOptionClass.end())
        }
        else //if (itPlanResponseId != m_pendingImplementationRouteRequests.end())
        {
            CERR_FILE_LINE_MSG("ERROR::processImplementationRouteResponseBase:: RoutePlanResponse received that was not expected, RoutePlanId[" << routePlanResponse->getResponseID() << "]")
        }
    }
}

std::shared_ptr<afrl::cmasi::Task> TaskServiceBase::generateTaskObject(const pugi::xml_node& taskNode)
{
    std::shared_ptr<afrl::cmasi::Task> taskPointer;

    pugi::xml_node taskRequestNode = taskNode.child("TaskRequest");
    if (!taskRequestNode.empty())
    {
        std::stringstream taskStringStream;
        taskRequestNode.first_child().print(taskStringStream);
        avtas::lmcp::Object* object = avtas::lmcp::xml::readXML(taskStringStream.str());
        if (object != nullptr)
        {
            auto task = dynamic_cast<afrl::cmasi::Task*> (object);
            taskPointer.reset(task);
        }
    }
    return (taskPointer);
}

std::shared_ptr<afrl::cmasi::EntityConfiguration> TaskServiceBase::generateEntityConfiguration(pugi::xml_node& entityConfigNode)
{
    std::shared_ptr<afrl::cmasi::EntityConfiguration> entityConfiguration;

    std::stringstream stringStream;
    entityConfigNode.print(stringStream);
    avtas::lmcp::Object* object = avtas::lmcp::xml::readXML(stringStream.str());
    if (object != nullptr)
    {
        entityConfiguration.reset(static_cast<afrl::cmasi::EntityConfiguration*> (object));
    }
    return (entityConfiguration);
}


}; //namespace task
}; //namespace service
}; //namespace uxas

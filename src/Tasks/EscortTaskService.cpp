// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_EscortTask.cpp
 * Author: derek
 * 
 * Created on March 7, 2016, 3:03 PM
 */


#include "EscortTaskService.h"

#include "Position.h"
#include "UnitConversions.h"

#include "avtas/lmcp/LmcpXMLReader.h"
#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/cmasi/LoiterAction.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/FollowPathCommand.h"
#include "afrl/impact/GroundVehicleConfiguration.h"
#include "afrl/impact/SurfaceVehicleConfiguration.h"
#include "afrl/impact/GroundVehicleState.h"
#include "afrl/impact/SurfaceVehicleState.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RouteResponse.h"
#include "uxas/messages/route/RouteConstraints.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"
#include "DpssDataTypes.h"
#include "TimeUtilities.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc


#define STRING_XML_ENTITY_STATES "EntityStates" //TODO:: define this in some global place

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "ESCT-ESCT-ESCT-ESCT:: EscortTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "ESCT-ESCT-ESCT-ESCT:: EscortTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
EscortTaskService::ServiceBase::CreationRegistrar<EscortTaskService>
EscortTaskService::s_registrar(EscortTaskService::s_registryServiceTypeNames());

EscortTaskService::EscortTaskService()
: TaskServiceBase(EscortTaskService::s_typeName(), EscortTaskService::s_directoryName())
{
};

EscortTaskService::~EscortTaskService()
{
};

bool
EscortTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isEscortTask(m_task.get()))
        {
            m_escortTask = std::static_pointer_cast<afrl::impact::EscortTask>(m_task);
            if (!m_escortTask)
            {
                sstrErrors << "ERROR:: **EscortTaskService::bConfigure failed to cast a EscortTask from the task pointer." << std::endl;
                CERR_FILE_LINE_MSG(sstrErrors.str())
                isSuccessful = false;
            }
        }
        else
        {
            sstrErrors << "ERROR:: **EscortTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a EscortTask." << std::endl;
            CERR_FILE_LINE_MSG(sstrErrors.str())
            isSuccessful = false;
        }
    } //isSuccessful
    if (isSuccessful)
    {
        pugi::xml_node entityStates = ndComponent.child(STRING_XML_ENTITY_STATES);
        if (entityStates)
        {
            for (auto ndEntityState = entityStates.first_child(); ndEntityState; ndEntityState = ndEntityState.next_sibling())
            {

                std::shared_ptr<afrl::cmasi::EntityState> entityState;
                std::stringstream stringStream;
                ndEntityState.print(stringStream);
                avtas::lmcp::Object* object = avtas::lmcp::xml::readXML(stringStream.str());
                if (object != nullptr)
                {
                    entityState.reset(static_cast<afrl::cmasi::EntityState*> (object));
                    object = nullptr;

                    if (entityState->getID() == m_escortTask->getSupportedEntityID())
                    {
                        m_supportedEntityStateLast = entityState;
                        break;
                    }
                }
            }
        }
    } //if(isSuccessful)

    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    addSubscriptionAddress(afrl::cmasi::FollowPathCommand::Subscription);
    addSubscriptionAddress(afrl::impact::LineOfInterest::Subscription);

    return (isSuccessful);
}

bool
EscortTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpObject);
    if (entityState)
    {
        if (entityState->getID() == m_escortTask->getSupportedEntityID())
        {
            m_supportedEntityStateLast = entityState;
        }
        m_idVsEntityState[entityState->getID()] = entityState;
    }
    else if (afrl::cmasi::isAutomationResponse(receivedLmcpObject))
    {
        auto ares = std::static_pointer_cast<afrl::cmasi::AutomationResponse>(receivedLmcpObject);
        for (auto v : ares->getMissionCommandList())
        {
            m_vehicleIdVsCurrentMission[v->getVehicleID()] = std::shared_ptr<afrl::cmasi::MissionCommand>(v->clone());
        }
    }
    else if (afrl::cmasi::isMissionCommand(receivedLmcpObject))
    {
        auto mish = std::static_pointer_cast<afrl::cmasi::MissionCommand>(receivedLmcpObject);
        m_vehicleIdVsCurrentMission[mish->getVehicleID()] = mish;
    }
    else if (afrl::cmasi::isFollowPathCommand(receivedLmcpObject))
    {
        auto fpc = std::static_pointer_cast<afrl::cmasi::FollowPathCommand>(receivedLmcpObject);
        auto path = std::shared_ptr<afrl::cmasi::MissionCommand>(new afrl::cmasi::MissionCommand);
        for (auto wp : fpc->getWaypointList())
        {
            path->getWaypointList().push_back(wp->clone());
        }
        m_vehicleIdVsCurrentMission[fpc->getVehicleID()] = path;
    }
    else if (afrl::impact::isLineOfInterest(receivedLmcpObject))
    {
        auto loi = std::static_pointer_cast<afrl::impact::LineOfInterest>(receivedLmcpObject);
        m_idVsLineOfInterest[loi->getLineID()] = loi;
    }
    return (false); // always false implies never terminating service from here
};

void EscortTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

    int64_t optionId(1);
    int64_t taskId(m_escortTask->getTaskID());

    if (isCalculateOption(taskId, optionId, m_escortTask->getEligibleEntities()))
    {
        optionId++;
    }

    std::string compositionString("+(");
    for (auto itOption = m_taskPlanOptions->getOptions().begin(); itOption != m_taskPlanOptions->getOptions().end(); itOption++)
    {
        compositionString += "p";
        compositionString += std::to_string((*itOption)->getOptionID());
        compositionString += " ";
    }
    compositionString += ")";

    m_taskPlanOptions->setComposition(compositionString);

    // send out the options
    if (isSuccessful)
    {
        auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
        sendSharedLmcpObjectBroadcastMessage(newResponse);
    }
};

bool EscortTaskService::isCalculateOption(const int64_t& taskId, int64_t& optionId, const std::vector<int64_t>& eligibleEntities)
{
    bool isSuccessful{true};

    if (m_supportedEntityStateLast)
    {
        // extract location of desired entity to track
        int64_t trackId = m_escortTask->getSupportedEntityID();
        std::shared_ptr<afrl::cmasi::Location3D> targetLocation;
        double targetHeading = 0.0;
        double targetSpeed = 0.0;
        if (m_idVsEntityState.find(trackId) != m_idVsEntityState.end())
        {
            targetLocation.reset(m_idVsEntityState[trackId]->getLocation()->clone());
            targetHeading = m_idVsEntityState[trackId]->getHeading();
            targetSpeed = m_idVsEntityState[trackId]->getGroundspeed();

            CalculateTargetPoint(targetLocation, targetHeading, targetSpeed, m_escortTask);

            auto taskOption = new uxas::messages::task::TaskOption;
            taskOption->setTaskID(taskId);
            taskOption->setOptionID(optionId);
            taskOption->getEligibleEntities() = eligibleEntities;
            taskOption->setStartLocation(targetLocation->clone());
            taskOption->setStartHeading(targetHeading);
            taskOption->setEndLocation(targetLocation->clone());
            taskOption->setEndHeading(targetHeading);
            auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
            m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
            m_taskPlanOptions->getOptions().push_back(taskOption);
            taskOption = nullptr; //just gave up ownership
        }
        else
        {
            // ERROR: could not find entity location that was requested to be tracked 
            isSuccessful = false;
        }
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::Task_EscortTask:: no watchedEntityState found for Entity[" << m_escortTask->getSupportedEntityID() << "]")
        isSuccessful = false;
    }

    return (isSuccessful);
}

void EscortTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    if (m_supportedEntityStateLast)
    {
        // extract location of desired entity to track
        int64_t trackId = m_escortTask->getSupportedEntityID();
        std::shared_ptr<afrl::cmasi::Location3D> targetLocation;
        double targetHeading = 0.0;
        double targetSpeed = 0.0;

        targetLocation.reset(m_supportedEntityStateLast->getLocation()->clone());
        targetHeading = m_supportedEntityStateLast->getHeading();
        targetSpeed = m_supportedEntityStateLast->getGroundspeed();

        // initialize throttle per vehicle
        if (m_throttle.find(entityState->getID()) == m_throttle.end())
        {
            m_throttle[entityState->getID()] = uxas::common::utilities::c_TimeUtilities::getTimeNow_ms();
        }

        // only send out every 2 seconds (even on fast simulation mode)
        if (!afrl::impact::isGroundVehicleState(entityState.get()) || m_throttle[entityState->getID()] + 2000 <= uxas::common::utilities::c_TimeUtilities::getTimeNow_ms())
        {
            m_throttle[entityState->getID()] = uxas::common::utilities::c_TimeUtilities::getTimeNow_ms();
        }
        else
        {
            return;
        }

        // look up speed to use for commanding vehicle
        double speed = entityState->getGroundspeed();
        if (m_idVsEntityConfiguration.find(entityState->getID()) != m_idVsEntityConfiguration.end())
        {
            speed = m_idVsEntityConfiguration[entityState->getID()]->getNominalSpeed();
        }

        CalculateTargetPoint(targetLocation, targetHeading, targetSpeed, m_escortTask);

        auto actionCommand = CalculateGimbalActions(entityState, targetLocation->getLatitude(), targetLocation->getLongitude());

        // build mini-mission of two waypoint with hover action at end
        auto missionCommand = new afrl::cmasi::MissionCommand;
        missionCommand->setCommandID(getUniqueEntitySendMessageId());
        missionCommand->setFirstWaypoint(1);
        missionCommand->setVehicleID(entityState->getID());
        auto wp = new afrl::cmasi::Waypoint;
        wp->setAltitude(entityState->getLocation()->getAltitude());
        wp->setAltitudeType(entityState->getLocation()->getAltitudeType());
        wp->setLatitude(targetLocation->getLatitude());
        wp->setLongitude(targetLocation->getLongitude());
        wp->setNextWaypoint(1);
        wp->setNumber(1);
        wp->setSpeed(speed);
        wp->setTurnType(afrl::cmasi::TurnType::TurnShort);
        wp->getAssociatedTasks().push_back(m_task->getTaskID());
        missionCommand->getWaypointList().push_back(wp);

        for (size_t a = 0; a < actionCommand->getVehicleActionList().size(); a++)
        {
            auto act = actionCommand->getVehicleActionList().at(a);
            wp->getVehicleActionList().push_back(act->clone());
        }
        missionCommand->getWaypointList().push_back(wp);

        // check if surface or ground vehicle
        if ((afrl::impact::isSurfaceVehicleState(entityState.get()) || afrl::impact::isGroundVehicleState(entityState.get())) && !missionCommand->getWaypointList().empty())
        {
            afrl::cmasi::Waypoint* hwp = wp->clone();
            hwp->setNumber(2);
            hwp->setNextWaypoint(2);
            missionCommand->getWaypointList().front()->setNextWaypoint(2);
            for (auto a : missionCommand->getWaypointList().front()->getVehicleActionList())
            {
                delete a;
            }
            missionCommand->getWaypointList().front()->getVehicleActionList().clear();
            missionCommand->getWaypointList().push_back(hwp);
        }
        else
        {
            for (auto wypt : missionCommand->getWaypointList())
            {
                delete wypt;
            }
            missionCommand->getWaypointList().clear();
        }

        // send response
        std::shared_ptr<avtas::lmcp::Object> pResponse;

        // single waypoint mission command instead of action (if possible)
        if (!missionCommand->getWaypointList().empty())
        {
            pResponse = std::shared_ptr<avtas::lmcp::Object>(missionCommand);
        }
        else
        {
            delete missionCommand;
            pResponse = std::static_pointer_cast<avtas::lmcp::Object>(actionCommand);
        }
        sendSharedLmcpObjectBroadcastMessage(pResponse);
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::Task_EscortTask:: no watchedEntityState found for Entity[" << m_escortTask->getSupportedEntityID() << "]")
    }
}

std::shared_ptr<afrl::cmasi::VehicleActionCommand> EscortTaskService::CalculateGimbalActions(const std::shared_ptr<afrl::cmasi::EntityState>& entityState, double lat, double lon)
{
    std::shared_ptr<afrl::cmasi::VehicleActionCommand> caction(new afrl::cmasi::VehicleActionCommand);

    double surveyRadius = m_loiterRadius_m;
    double surveySpeed = entityState->getGroundspeed();
    auto surveyType = afrl::cmasi::LoiterType::Circular;
    std::vector<int64_t> gimbalId;

    if (m_idVsEntityConfiguration.find(entityState->getID()) != m_idVsEntityConfiguration.end())
    {
        surveySpeed = m_idVsEntityConfiguration[entityState->getID()]->getNominalSpeed();
        // find all gimbals to steer
        for (size_t a = 0; a < m_idVsEntityConfiguration[entityState->getID()]->getPayloadConfigurationList().size(); a++)
        {
            auto payload = m_idVsEntityConfiguration[entityState->getID()]->getPayloadConfigurationList().at(a);
            if (afrl::cmasi::isGimbalConfiguration(payload))
            {
                gimbalId.push_back(payload->getPayloadID());
            }
        }

        // calculate proper radius
        if (afrl::impact::isGroundVehicleConfiguration(m_idVsEntityConfiguration[entityState->getID()].get()) ||
                afrl::impact::isSurfaceVehicleConfiguration(m_idVsEntityConfiguration[entityState->getID()].get()))
        {
            surveyRadius = 0.0;
            surveyType = afrl::cmasi::LoiterType::Hover;
        }
        else if (afrl::cmasi::isAirVehicleConfiguration(m_idVsEntityConfiguration[entityState->getID()].get()))
        {
            double speed = m_idVsEntityConfiguration[entityState->getID()]->getNominalSpeed();
            double bank = 25.0 * n_Const::c_Convert::dDegreesToRadians();
            // Note: R = V/omega for coordinated turn omega = g*tan(phi)/V
            // Therefore: R = V^2/(g*tan(phi))
            surveyRadius = speed * speed / (9.80665 * tan(bank));
            // round up to the nearest 100m
            surveyRadius = std::ceil(surveyRadius / 100.0)*100.0;

            // TODO: sometimes the loiter radius seems to change size, so hard-code
            surveyRadius = m_loiterRadius_m;
        }
    }

    afrl::cmasi::LoiterAction* surveyAction = new afrl::cmasi::LoiterAction;
    surveyAction->setLocation(new afrl::cmasi::Location3D());
    surveyAction->getLocation()->setLatitude(lat);
    surveyAction->getLocation()->setLongitude(lon);
    surveyAction->getLocation()->setAltitude(entityState->getLocation()->getAltitude());
    surveyAction->getLocation()->setAltitudeType(entityState->getLocation()->getAltitudeType());
    surveyAction->setAirspeed(surveySpeed);
    surveyAction->setRadius(surveyRadius);
    surveyAction->setDirection(afrl::cmasi::LoiterDirection::CounterClockwise);
    surveyAction->setDuration(-1);
    surveyAction->setLoiterType(surveyType);
    surveyAction->getAssociatedTaskList().push_back(m_task->getTaskID());
    caction->getVehicleActionList().push_back(surveyAction);

    // steer all gimbals
    for (size_t g = 0; g < gimbalId.size(); g++)
    {
        afrl::cmasi::GimbalStareAction* gimbalAction = new afrl::cmasi::GimbalStareAction;
        gimbalAction->setDuration(-1);
        gimbalAction->setPayloadID(gimbalId.at(g));
        gimbalAction->setStarepoint(m_supportedEntityStateLast->getLocation()->clone());
        gimbalAction->getAssociatedTaskList().push_back(m_task->getTaskID());
        caction->getVehicleActionList().push_back(gimbalAction->clone());
    }

    return caction;
}

void EscortTaskService::CalculateTargetPoint(std::shared_ptr<afrl::cmasi::Location3D>& targetLocation, double targetHeading, double targetSpeed, std::shared_ptr<afrl::impact::EscortTask>& task)
{
    // decipher path that the supported entity is following
    std::vector<afrl::cmasi::Location3D*> path;
    if (task->getRouteID() == 0)
    {
        // look up from known waypoints
        if (m_vehicleIdVsCurrentMission.find(task->getSupportedEntityID()) != m_vehicleIdVsCurrentMission.end())
        {
            path.assign(m_vehicleIdVsCurrentMission[task->getSupportedEntityID()]->getWaypointList().begin(),
                    m_vehicleIdVsCurrentMission[task->getSupportedEntityID()]->getWaypointList().end());
        }
        else if (!task->getPrescribedWaypoints().empty())
        {
            path.assign(task->getPrescribedWaypoints().begin(), task->getPrescribedWaypoints().end());
        }
        else
        {
            // zero route ID and empty prescribed path, so try to determine
            // from set of known lines of interest
            double ldist = -1.0;
            int64_t lId = 0;
            for (auto line : m_idVsLineOfInterest)
            {
                double dist = DistanceToLine(targetLocation, line.second);
                if (dist > 0.0 && (ldist < 0 || dist < ldist))
                {
                    ldist = dist;
                    lId = line.first;
                }
            }

            if (lId && m_idVsLineOfInterest.find(lId) != m_idVsLineOfInterest.end())
            {
                path.assign(m_idVsLineOfInterest[lId]->getLine().begin(), m_idVsLineOfInterest[lId]->getLine().end());
                if (fabs(targetSpeed) < 1.0)
                {
                    // target is stationary, reverse the line if closer to end than beginning
                    uxas::common::utilities::CUnitConversions flatEarth;
                    double north, east;

                    flatEarth.ConvertLatLong_degToNorthEast_m(targetLocation->getLatitude(), targetLocation->getLongitude(), north, east);
                    Dpss_Data_n::xyPoint target(east, north);

                    std::vector< Dpss_Data_n::xyPoint > linpath;
                    for (auto p : path)
                    {
                        flatEarth.ConvertLatLong_degToNorthEast_m(p->getLatitude(), p->getLongitude(), north, east);
                        Dpss_Data_n::xyPoint pt(east, north);
                        linpath.push_back(pt);
                    }

                    double mindist = -1.0;
                    double totallength = 0.0;
                    double minlength = 0.0;
                    for (size_t b = 1, a = 0; b < linpath.size(); a++, b++)
                    {
                        Dpss_Data_n::Segment q(linpath.at(a), linpath.at(b));
                        totallength += q.len();
                        double segDist = q.distToClosestPoint(target);

                        // check heading congruence
                        if ((mindist < 0.0 || segDist < mindist))
                        {
                            mindist = segDist;
                            minlength = totallength + target.dist(linpath.at(a));
                        }
                        totallength += q.len();
                    }
                    if (totallength > 1.0 && minlength / totallength > 0.5)
                    {
                        std::reverse(path.begin(), path.end());
                    }
                }
                else if (FlipLine(targetLocation, targetHeading, m_idVsLineOfInterest[lId]))
                {
                    std::reverse(path.begin(), path.end());
                }
            }
        }
    }
    else
    {
        // look up from lines of interest
        int64_t lineId = task->getRouteID();
        if (m_idVsLineOfInterest.find(lineId) != m_idVsLineOfInterest.end())
        {
            path.assign(m_idVsLineOfInterest[lineId]->getLine().begin(), m_idVsLineOfInterest[lineId]->getLine().end());
        }
    }

    if (!path.empty())
    {
        // project current target location onto path, linearize first
        uxas::common::utilities::CUnitConversions flatEarth;
        double north, east;

        flatEarth.ConvertLatLong_degToNorthEast_m(targetLocation->getLatitude(), targetLocation->getLongitude(), north, east);
        Dpss_Data_n::xyPoint target(east, north);

        std::vector< Dpss_Data_n::xyPoint > linpath;
        for (auto p : path)
        {
            flatEarth.ConvertLatLong_degToNorthEast_m(p->getLatitude(), p->getLongitude(), north, east);
            Dpss_Data_n::xyPoint pt(east, north);
            linpath.push_back(pt);
        }

        // wrap heading for heading check (note, degrees from north)
        targetHeading = fmod(targetHeading, 360.0);
        if (targetHeading < 0.0)
        {
            targetHeading += 360.0;
        }

        double mindist = -1.0;
        Dpss_Data_n::xyPoint projPt(target);
        size_t segmentEndIndex = 0;
        size_t segmentStartIndex = 0;
        for (size_t b = 1, a = 0; b < linpath.size(); a++, b++)
        {
            Dpss_Data_n::Segment q(linpath.at(a), linpath.at(b));
            double segDist = q.distToClosestPoint(target);
            if (mindist < 0.0 || segDist < mindist)
            {
                // convert segment angle to from-north in degrees
                double segmentHeading = (n_Const::c_Convert::dPiO2() - q.angle()) * n_Const::c_Convert::dRadiansToDegrees();
                if (segmentHeading < 0.0)
                {
                    segmentHeading += 360.0;
                }
                double headingDelta = targetHeading - segmentHeading;
                if (headingDelta > 180.0)
                {
                    headingDelta -= 360.0;
                }
                if (headingDelta < -180.0)
                {
                    headingDelta += 360.0;
                }

                // check heading congruence
                if (fabs(headingDelta) < 90.0 || fabs(targetSpeed) < 1.0)
                {
                    projPt = q.closestPoint(target);
                    mindist = segDist;
                    segmentEndIndex = b;
                    segmentStartIndex = a;
                }
            }
        }

        if (task->getStandoffDistance() >= -0.01)
        {
            double accumulatedDist = projPt.dist(linpath.at(segmentEndIndex));
            while (accumulatedDist < task->getStandoffDistance() && (segmentEndIndex + 1) < linpath.size())
            {
                projPt = linpath.at(segmentEndIndex);
                accumulatedDist += projPt.dist(linpath.at(segmentEndIndex + 1));
                segmentEndIndex++;
            }

            if (accumulatedDist >= task->getStandoffDistance())
            {
                // back off by the difference
                double backOff = accumulatedDist - task->getStandoffDistance();
                projPt -= linpath.at(segmentEndIndex);
                if (projPt.len() > 1e-2 && backOff <= (projPt.len() + 1.0))
                {
                    projPt *= backOff / projPt.len();
                    projPt += linpath.at(segmentEndIndex);
                }
                else
                {
                    projPt = linpath.at(segmentEndIndex);
                }
            }
            else
            {
                // just wait at the end
                projPt = linpath.back();
            }
        }
        else
        {
            double accumulatedDist = projPt.dist(linpath.at(segmentStartIndex));
            while (accumulatedDist < fabs(task->getStandoffDistance()) && segmentStartIndex > 0)
            {
                projPt = linpath.at(segmentStartIndex);
                accumulatedDist += projPt.dist(linpath.at(segmentStartIndex - 1));
                segmentStartIndex--;
            }

            if (accumulatedDist >= fabs(task->getStandoffDistance()))
            {
                // back off by the difference
                double backOff = accumulatedDist + task->getStandoffDistance();
                projPt -= linpath.at(segmentStartIndex);
                if (projPt.len() > 1e-2 && backOff <= (projPt.len() + 1.0))
                {
                    projPt *= backOff / projPt.len();
                    projPt += linpath.at(segmentStartIndex);
                }
                else
                {
                    projPt = linpath.at(segmentStartIndex);
                }
            }
            else
            {
                // just wait at the end
                projPt = linpath.front();
            }
        }

        // back to lat/lon
        double lat, lon;
        flatEarth.ConvertNorthEast_mToLatLong_deg(projPt.y, projPt.x, lat, lon);
        targetLocation->setLatitude(lat);
        targetLocation->setLongitude(lon);
    }
}

double EscortTaskService::DistanceToLine(std::shared_ptr<afrl::cmasi::Location3D>& loc, std::shared_ptr<afrl::impact::LineOfInterest>& path)
{
    uxas::common::utilities::CUnitConversions flatEarth;
    double north, east;

    flatEarth.ConvertLatLong_degToNorthEast_m(loc->getLatitude(), loc->getLongitude(), north, east);
    Dpss_Data_n::xyPoint target(east, north);

    std::vector< Dpss_Data_n::xyPoint > linpath;
    for (auto p : path->getLine())
    {
        flatEarth.ConvertLatLong_degToNorthEast_m(p->getLatitude(), p->getLongitude(), north, east);
        Dpss_Data_n::xyPoint pt(east, north);
        linpath.push_back(pt);
    }

    double mindist = -1.0;
    for (size_t b = 1, a = 0; b < linpath.size(); a++, b++)
    {
        Dpss_Data_n::Segment q(linpath.at(a), linpath.at(b));
        double segDist = q.distToClosestPoint(target);
        if (mindist < 0.0 || segDist < mindist)
        {
            mindist = segDist;
        }
    }

    return mindist;
}

bool EscortTaskService::FlipLine(std::shared_ptr<afrl::cmasi::Location3D>& loc, double heading, std::shared_ptr<afrl::impact::LineOfInterest>& path)
{
    uxas::common::utilities::CUnitConversions flatEarth;
    double north, east;

    flatEarth.ConvertLatLong_degToNorthEast_m(loc->getLatitude(), loc->getLongitude(), north, east);
    Dpss_Data_n::xyPoint target(east, north);

    std::vector< Dpss_Data_n::xyPoint > linpath;
    for (auto p : path->getLine())
    {
        flatEarth.ConvertLatLong_degToNorthEast_m(p->getLatitude(), p->getLongitude(), north, east);
        Dpss_Data_n::xyPoint pt(east, north);
        linpath.push_back(pt);
    }

    // forward direction
    double minforwarddist = -1.0;
    for (size_t b = 1, a = 0; b < linpath.size(); a++, b++)
    {
        Dpss_Data_n::Segment q(linpath.at(a), linpath.at(b));
        double segDist = q.distToClosestPoint(target);

        // convert segment angle to from-north in degrees
        double segmentHeading = (n_Const::c_Convert::dPiO2() - q.angle()) * n_Const::c_Convert::dRadiansToDegrees();
        if (segmentHeading < 0.0)
        {
            segmentHeading += 360.0;
        }
        double headingDelta = heading - segmentHeading;
        if (headingDelta > 180.0)
        {
            headingDelta -= 360.0;
        }
        if (headingDelta < -180.0)
        {
            headingDelta += 360.0;
        }

        // check heading congruence
        if (fabs(headingDelta) < 90.0 && (minforwarddist < 0.0 || segDist < minforwarddist))
        {
            minforwarddist = segDist;
        }
    }

    // reverse direction
    double minreversedist = -1.0;
    if (linpath.size() >= 2)
    {
        for (size_t b = linpath.size() - 1, a = linpath.size() - 2; b > 0; a--, b--)
        {
            Dpss_Data_n::Segment q(linpath.at(b), linpath.at(a));
            double segDist = q.distToClosestPoint(target);

            // convert segment angle to from-north in degrees
            double segmentHeading = (n_Const::c_Convert::dPiO2() - q.angle()) * n_Const::c_Convert::dRadiansToDegrees();
            if (segmentHeading < 0.0)
            {
                segmentHeading += 360.0;
            }
            double headingDelta = heading - segmentHeading;
            if (headingDelta > 180.0)
            {
                headingDelta -= 360.0;
            }
            if (headingDelta < -180.0)
            {
                headingDelta += 360.0;
            }

            // check heading congruence
            if (fabs(headingDelta) < 90.0 && (minreversedist < 0.0 || segDist < minreversedist))
            {
                minreversedist = segDist;
            }
        }
    }

    if (minreversedist < 0.0)
        return false;

    if ((minforwarddist > 0.0 && minreversedist < minforwarddist))
        return true;

    return false;
}


}; //namespace task
}; //namespace service
}; //namespace uxas

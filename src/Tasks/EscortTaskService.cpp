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
#include "afrl/vehicles/GroundVehicleConfiguration.h"
#include "afrl/vehicles/SurfaceVehicleConfiguration.h"
#include "afrl/vehicles/GroundVehicleState.h"
#include "afrl/vehicles/SurfaceVehicleState.h"
#include "uxas/messages/task/TaskOption.h"


#include "Constants/Convert.h"
#include "DpssDataTypes.h"
#include "TimeUtilities.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc



namespace uxas
{
namespace service
{
namespace task
{
EscortTaskService::ServiceBase::CreationRegistrar<EscortTaskService>
EscortTaskService::s_registrar(EscortTaskService::s_registryServiceTypeNames());

EscortTaskService::EscortTaskService()
: DynamicTaskServiceBase(EscortTaskService::s_typeName(), EscortTaskService::s_directoryName())
{
};

EscortTaskService::~EscortTaskService()
{
};

bool
EscortTaskService::configureDynamicTask(const pugi::xml_node& ndComponent)

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
                UXAS_LOG_ERROR("**EscortTaskService::bConfigure failed to cast a EscortTask from the task pointer.");
                isSuccessful = false;
            }
        }
        else
        {
            UXAS_LOG_ERROR("ERROR:: **EscortTaskService::bConfigure failed: taskObject[" + m_task->getFullLmcpTypeName() + "] is not a EscortTask.");
            isSuccessful = false;
        }
    } //isSuccessful
    if (isSuccessful)
    {
        if (m_entityStates.find(m_escortTask->getSupportedEntityID()) != m_entityStates.end())
        {
            m_supportedEntityStateLast = m_entityStates[m_escortTask->getSupportedEntityID()];
        }
        else
        {
            UXAS_LOG_ERROR("Escort Task ", m_escortTask->getTaskID(), " supported entity ", m_escortTask->getSupportedEntityID(), " Does Not Exist");
            isSuccessful = false;
        }

    } //if(isSuccessful)

    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    addSubscriptionAddress(afrl::cmasi::FollowPathCommand::Subscription);
    addSubscriptionAddress(afrl::impact::LineOfInterest::Subscription);

    return (isSuccessful);
}


bool EscortTaskService::processRecievedLmcpMessageDynamicTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpObject);
    if (entityState)
    {
        if (entityState->getID() == m_escortTask->getSupportedEntityID())
        {
            m_supportedEntityStateLast = entityState;
        }
    }
    else if (afrl::cmasi::isAutomationResponse(receivedLmcpObject))
    {
        auto ares = std::static_pointer_cast<afrl::cmasi::AutomationResponse>(receivedLmcpObject);
        for (auto v : ares->getMissionCommandList())
        {
            m_currentMissions[v->getVehicleID()] = std::shared_ptr<afrl::cmasi::MissionCommand>(v->clone());
        }
    }
    else if (afrl::cmasi::isMissionCommand(receivedLmcpObject))
    {
        auto mish = std::static_pointer_cast<afrl::cmasi::MissionCommand>(receivedLmcpObject);
        m_currentMissions[mish->getVehicleID()] = mish;
    }
    else if (afrl::cmasi::isFollowPathCommand(receivedLmcpObject))
    {
        auto fpc = std::static_pointer_cast<afrl::cmasi::FollowPathCommand>(receivedLmcpObject);
        auto path = std::shared_ptr<afrl::cmasi::MissionCommand>(new afrl::cmasi::MissionCommand);
        for (auto wp : fpc->getWaypointList())
        {
            path->getWaypointList().push_back(wp->clone());
        }
        m_currentMissions[fpc->getVehicleID()] = path;
    }
    else if (afrl::impact::isLineOfInterest(receivedLmcpObject))
    {
        auto loi = std::static_pointer_cast<afrl::impact::LineOfInterest>(receivedLmcpObject);
        m_linesOfInterest[loi->getLineID()] = loi;
    }
    return (false); // always false implies never terminating service from here
    int64_t optionId(TaskOptionClass::m_firstOptionId);
}


std::shared_ptr<afrl::cmasi::Location3D> EscortTaskService::calculateTargetLocation(const std::shared_ptr<afrl::cmasi::EntityState> entityState)
{
    std::shared_ptr<afrl::cmasi::Location3D> targetLocation;
    if (!m_supportedEntityStateLast) {
        return targetLocation;
    }
    double targetHeading = 0.0;
    double targetSpeed = 0.0;

    targetLocation.reset(m_supportedEntityStateLast->getLocation()->clone());
    targetHeading = m_supportedEntityStateLast->getHeading();
    targetSpeed = m_supportedEntityStateLast->getGroundspeed();

    double speed = entityState->getGroundspeed();
    if (m_entityConfigurations.find(entityState->getID()) != m_entityConfigurations.end())
    {
        speed = m_entityConfigurations[entityState->getID()]->getNominalSpeed();
    }

    CalculateTargetPoint(targetLocation, targetHeading, targetSpeed, m_escortTask);
    return targetLocation;
}



void EscortTaskService::CalculateTargetPoint(std::shared_ptr<afrl::cmasi::Location3D>& targetLocation, double targetHeading, double targetSpeed, std::shared_ptr<afrl::impact::EscortTask>& task)
{
    //if standoff is zero, don't mess with the targetLocation
    if (abs(task->getStandoffDistance() - .001) <  .1)
    {
        return;
    }

    // decipher path that the supported entity is following
    std::vector<afrl::cmasi::Location3D*> path;
    if (task->getRouteID() == 0)
    {
        // look up from known waypoints
        if (m_currentMissions.find(task->getSupportedEntityID()) != m_currentMissions.end())
        {
            path.assign(m_currentMissions[task->getSupportedEntityID()]->getWaypointList().begin(),
                    m_currentMissions[task->getSupportedEntityID()]->getWaypointList().end());
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
            for (auto line : m_linesOfInterest)
            {
                double dist = DistanceToLine(targetLocation, line.second);
                if (dist > 0.0 && (ldist < 0 || dist < ldist))
                {
                    ldist = dist;
                    lId = line.first;
                }
            }

            if (lId && m_linesOfInterest.find(lId) != m_linesOfInterest.end())
            {
                path.assign(m_linesOfInterest[lId]->getLine().begin(), m_linesOfInterest[lId]->getLine().end());
                if (fabs(targetSpeed) < 1.0)
                {
                    // target is stationary, reverse the line if closer to end than beginning
                    common::utilities::CUnitConversions flatEarth;
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
                else if (FlipLine(targetLocation, targetHeading, m_linesOfInterest[lId]))
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
        if (m_linesOfInterest.find(lineId) != m_linesOfInterest.end())
        {
            path.assign(m_linesOfInterest[lineId]->getLine().begin(), m_linesOfInterest[lineId]->getLine().end());
        }
    }

    if (!path.empty())
    {
        // project current target location onto path, linearize first
        common::utilities::CUnitConversions flatEarth;
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
    common::utilities::CUnitConversions flatEarth;
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
    common::utilities::CUnitConversions flatEarth;
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

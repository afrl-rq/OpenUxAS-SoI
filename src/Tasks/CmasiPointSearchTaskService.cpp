// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_CmasiPointSearch.cpp
 * Author: steve
 * 
 * Created on August 31, 2015, 6:17 PM
 */


#include "CmasiPointSearchTaskService.h"

#include "Position.h"
#include "UnitConversions.h"

#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RouteResponse.h"
#include "uxas/messages/route/RouteConstraints.h"

#ifdef AFRL_INTERNAL_ENABLED
#include "afrl/famus/PointSearchTask.h"
#endif

#include "pugixml.hpp"
#include "Constants/Convert.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc


#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "CMPS-CMPS-CMPS-CMPS:: CmasiPointSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "CMPS-CMPS-CMPS-CMPS:: CmasiPointSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
CmasiPointSearchTaskService::ServiceBase::CreationRegistrar<CmasiPointSearchTaskService>
CmasiPointSearchTaskService::s_registrar(CmasiPointSearchTaskService::s_registryServiceTypeNames());

CmasiPointSearchTaskService::CmasiPointSearchTaskService()
: TaskServiceBase(CmasiPointSearchTaskService::s_typeName(), CmasiPointSearchTaskService::s_directoryName()) {
    //UXAS_LOG_INFORM_ASSIGNMENT("*** CONSTRUCTOR m_networkId[",m_networkId,"] ***");
    m_isMakeTransitionWaypointsActive = true;
};

CmasiPointSearchTaskService::~CmasiPointSearchTaskService() {
    //UXAS_LOG_INFORM_ASSIGNMENT("*** DESTRUCTOR ***");
};

bool
CmasiPointSearchTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    m_pointSearchTask = std::dynamic_pointer_cast<afrl::cmasi::PointSearchTask>(m_task);
    if (!m_pointSearchTask)
    {
        UXAS_LOG_ERROR("ERROR:: **CmasiPointSearchTaskService::bConfigure failed: taskObject[" + m_task->getFullLmcpTypeName() + "] is not a PointSearchTask.");
        return false;
    }
    return true;
}

void CmasiPointSearchTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

    int64_t optionId(TaskOptionClass::m_firstOptionId);
    int64_t taskId(m_pointSearchTask->getTaskID());

    double wedgeDirectionIncrement(n_Const::c_Convert::dPiO8());

    //ViewAngleList
    if (!m_pointSearchTask->getViewAngleList().empty())
    {
        for (auto itWedge = m_pointSearchTask->getViewAngleList().begin();
                itWedge != m_pointSearchTask->getViewAngleList().end();
                itWedge++)
        {
            double dHeadingCenterline_rad = n_Const::c_Convert::dNormalizeAngleRad(((*itWedge)->getAzimuthCenterline() * n_Const::c_Convert::dDegreesToRadians()), 0.0);
            //centerline angle is between 0 and 2PI
            double dHeadingStart_rad = dHeadingCenterline_rad - ((*itWedge)->getAzimuthExtent() / 2.0) * n_Const::c_Convert::dDegreesToRadians();
            double dHeadingEnd_rad = dHeadingCenterline_rad + ((*itWedge)->getAzimuthExtent() / 2.0) * n_Const::c_Convert::dDegreesToRadians();
            double dHeadingCurrent_rad(dHeadingStart_rad);
            double dHeadingTarget_rad = (n_Const::c_Convert::bCompareDouble(dHeadingEnd_rad, dHeadingStart_rad, n_Const::c_Convert::enGreaterEqual, 1.0e-5)) ? (dHeadingEnd_rad) : (n_Const::c_Convert::dTwoPi());
            while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
            {
                if (isCalculateOption(taskId, optionId, dHeadingCurrent_rad))
                {
                    optionId++;
                }
                dHeadingCurrent_rad += wedgeDirectionIncrement;
            }
            //need to see if wedge straddles the 0/2PI direction
            if ((!n_Const::c_Convert::bCompareDouble(dHeadingEnd_rad, dHeadingTarget_rad, n_Const::c_Convert::enEqual)) &&
                    (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, n_Const::c_Convert::dTwoPi(), n_Const::c_Convert::enEqual)))
            {
                dHeadingCurrent_rad = 0.0;
                dHeadingTarget_rad = dHeadingEnd_rad;
                while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
                {
                    if (isCalculateOption(taskId, optionId, dHeadingCurrent_rad))
                    {
                        optionId++;
                    }
                    dHeadingCurrent_rad += wedgeDirectionIncrement;
                }
            }
        }
    }
    else
    {
        // no set wedge, so standoff from any angle
        double dHeadingCurrent_rad = 0.0;
        double dHeadingTarget_rad = n_Const::c_Convert::dTwoPi() - wedgeDirectionIncrement;
        while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
        {
            if (isCalculateOption(taskId, optionId, dHeadingCurrent_rad))
            {
                optionId++;
            }
            dHeadingCurrent_rad += wedgeDirectionIncrement;
        }
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

bool CmasiPointSearchTaskService::isCalculateOption(const int64_t& taskId, int64_t& optionId, const double& wedgeHeading_rad)
{
    bool isSuccessful{true};

    uxas::common::utilities::CUnitConversions unitConversions;
    double standoffDistance = m_pointSearchTask->getStandoffDistance();

    auto taskOption = new uxas::messages::task::TaskOption;
    auto startEndHeading_deg = n_Const::c_Convert::dNormalizeAngleRad((wedgeHeading_rad + n_Const::c_Convert::dPi()), 0.0) * n_Const::c_Convert::dRadiansToDegrees(); // [0,2PI) 
    taskOption->setStartHeading(startEndHeading_deg);
    taskOption->setEndHeading(startEndHeading_deg);
    
    if (n_Const::c_Convert::bCompareDouble(standoffDistance, 0.0, n_Const::c_Convert::enLessEqual))
    {
        taskOption->setTaskID(taskId);
        taskOption->setOptionID(optionId);
        //taskOption->setCost();    // defaults to 0.0
        taskOption->setStartLocation(m_pointSearchTask->getSearchLocation()->clone());
        taskOption->setEndLocation(m_pointSearchTask->getSearchLocation()->clone());
        for(auto itEligibleEntities : m_speedAltitudeVsEligibleEntityIdsRequested)
            for( auto id : itEligibleEntities.second )
                taskOption->getEligibleEntities().push_back(id);
        taskOption->setCost(0);
        auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
        m_taskPlanOptions->getOptions().push_back(taskOption);
        return true;
    }

    taskOption->setTaskID(taskId);
    taskOption->setOptionID(optionId);

    //find standoff (start) location
    n_FrameworkLib::CPosition position(m_pointSearchTask->getSearchLocation()->getLatitude() * n_Const::c_Convert::dDegreesToRadians(),
                                        m_pointSearchTask->getSearchLocation()->getLongitude() * n_Const::c_Convert::dDegreesToRadians(),
                                        0.0, 0.0);
    double newNorth_m = standoffDistance * cos(wedgeHeading_rad) + position.m_north_m;
    double newEast_m = standoffDistance * sin(wedgeHeading_rad) + position.m_east_m;
    double latitude_rad(0.0);
    double longitude_rad(0.0);

    unitConversions.ConvertNorthEast_mToLatLong_rad(newNorth_m, newEast_m, latitude_rad, longitude_rad);
    auto startLocation = new afrl::cmasi::Location3D();
    startLocation->setLatitude(latitude_rad * n_Const::c_Convert::dRadiansToDegrees());
    startLocation->setLongitude(longitude_rad * n_Const::c_Convert::dRadiansToDegrees());
    taskOption->setStartLocation(startLocation);
    startLocation = nullptr; // just gave up ownership
    taskOption->setEndLocation(m_pointSearchTask->getSearchLocation()->clone());

    auto routePlan = std::make_shared<uxas::messages::route::RoutePlan>();

    int64_t waypointNumber = 1;
    auto waypoint = new afrl::cmasi::Waypoint();
    waypoint->setNumber(waypointNumber);
    waypoint->setLatitude(taskOption->getStartLocation()->getLatitude());
    waypoint->setLongitude(taskOption->getStartLocation()->getLongitude());
    waypoint->setAltitude(taskOption->getStartLocation()->getAltitude());
    routePlan->getWaypoints().push_back(waypoint);
    waypoint = nullptr; // gave up ownership
    
    waypointNumber++;
    waypoint = new afrl::cmasi::Waypoint();
    waypoint->setNumber(waypointNumber);
    waypoint->setLatitude(taskOption->getEndLocation()->getLatitude());
    waypoint->setLongitude(taskOption->getEndLocation()->getLongitude());
    waypoint->setAltitude(taskOption->getEndLocation()->getAltitude());
    routePlan->getWaypoints().push_back(waypoint);

    routePlan->setRouteID(TaskOptionClass::m_firstImplementationRouteId);
//        double costForward_ms = static_cast<int64_t> (((nominalSpeed_mps > 0.0) ? (standoffDistance / nominalSpeed_mps) : (0.0))*1000.0);
    int64_t costForward_ms = 0;
    routePlan->setRouteCost(costForward_ms);


    auto taskOptionLocal = taskOption->clone();
    taskOptionLocal->setOptionID(optionId);
    for (auto itEligibleEntites = m_speedAltitudeVsEligibleEntityIdsRequested.begin(); itEligibleEntites != m_speedAltitudeVsEligibleEntityIdsRequested.end(); itEligibleEntites++)
    {
        taskOptionLocal->getEligibleEntities() = itEligibleEntites->second;
        if (itEligibleEntites->first.first > 0)
        {
            taskOptionLocal->setCost(static_cast<int64_t>( standoffDistance / static_cast<double>(itEligibleEntites->first.first) * 1000.0));
        }
        auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOptionLocal->clone());
        auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
        pTaskOptionClass->m_orderedRouteIdVsPlan[routePlan->getRouteID()] = routePlan;
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
        m_taskPlanOptions->getOptions().push_back(taskOptionLocal);
        // start a new option
        optionId++;
        taskOptionLocal = taskOption->clone();
        taskOptionLocal->setOptionID(optionId);
    } //for(auto itSpeedId=m_speedVsVehicleId.begin();itSpeedId!=m_speedVsVehicleId.end();itSpeedId++)
    if (taskOptionLocal != nullptr)
    {
        delete taskOptionLocal;
        taskOptionLocal = nullptr;
    }
    if (taskOption != nullptr)
    {
        delete taskOption;
        taskOption = nullptr;
    }

    return (isSuccessful);
}

void CmasiPointSearchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    // TODO: point all gimbals, not simply the last one listed
    int64_t gimbalId = 0;
    if (m_entityConfigurations.find(entityState->getID()) != m_entityConfigurations.end())
    {
        auto cfg = m_entityConfigurations[entityState->getID()];
        for (auto payload : cfg->getPayloadConfigurationList())
            if (afrl::cmasi::isGimbalConfiguration(payload))
                gimbalId = payload->getPayloadID();
    }

    // we are at an active waypoint
    // point the camera at the search point
    auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
    //vehicleActionCommand->setCommandID();
    vehicleActionCommand->setVehicleID(entityState->getID());
    //vehicleActionCommand->setStatus();
    auto gimbalStareAction = new afrl::cmasi::GimbalStareAction;
    gimbalStareAction->setPayloadID(gimbalId);
    gimbalStareAction->setStarepoint(m_pointSearchTask->getSearchLocation()->clone());
    vehicleActionCommand->getVehicleActionList().push_back(gimbalStareAction);
    gimbalStareAction = nullptr; //gave up ownership
    // send out the response
    auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(vehicleActionCommand);
    sendSharedLmcpObjectBroadcastMessage(newMessage);
}

bool CmasiPointSearchTaskService::isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
    std::shared_ptr<TaskOptionClass>& taskOptionClass,
    int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route)
{
#ifdef AFRL_INTERNAL_ENABLED
    // override speed as necessary
    if(afrl::famus::isPointSearchTask(m_task.get()))
    {
        auto famusTask = std::static_pointer_cast<afrl::famus::PointSearchTask>(m_task);
        if(famusTask->getDesiredSpeed() > 1e-4)
            for(auto wp : taskImplementationResponse->getTaskWaypoints())
                wp->setSpeed(famusTask->getDesiredSpeed());

        if(famusTask->getEnforceAltitude())
        {
            for(auto wp : taskImplementationResponse->getTaskWaypoints())
            {
                wp->setAltitude(famusTask->getAltitude());
                wp->setAltitudeType(famusTask->getAltitudeType());
            }
        }
        return true;
    }
#endif

    return false;
}


}; //namespace task
}; //namespace service
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
* File:   MustFlyTaskService.cpp
* Author: colin
*
* Created on May 4, 2017
*/


#include "MustFlyTaskService.h"

#include "Position.h"
#include "FileSystemUtilities.h"
#include "Polygon.h"
#include "FlatEarth.h"

#include "afrl/cmasi/Circle.h"
#include "uxas/messages/task/SensorFootprintResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/ROUTE.h"

#ifdef AFRL_INTERNAL_ENABLED
#include "afrl/famus/MustFlyTask.h"
#endif

#include <sstream>      //std::stringstream
#include <iomanip>  //setfill


namespace uxas
{
namespace service
{
namespace task
{
MustFlyTaskService::ServiceBase::CreationRegistrar<MustFlyTaskService>
MustFlyTaskService::s_registrar(MustFlyTaskService::s_registryServiceTypeNames());

MustFlyTaskService::MustFlyTaskService()
    : TaskServiceBase(MustFlyTaskService::s_typeName(), MustFlyTaskService::s_directoryName()) {}

MustFlyTaskService::~MustFlyTaskService() {}

bool MustFlyTaskService::configureTask(const pugi::xml_node& ndComponent)
{
    m_mustFlyTask = std::dynamic_pointer_cast<afrl::cmasi::MustFlyTask>(m_task);
    if (!m_mustFlyTask)
    {
        UXAS_LOG_ERROR("ERROR:: **MustFlyTaskService::bConfigure failed: taskObject[" + m_task->getFullLmcpTypeName() + "] is not a MustFlyTask.");
        return false;
    }
    addSubscriptionAddress(uxas::messages::route::RouteResponse::Subscription);
    return true;
}

void MustFlyTaskService::buildTaskPlanOptions()
{
    int64_t optionId = TaskOptionClass::m_firstOptionId;

#ifdef AFRL_INTERNAL_ENABLED
    if(afrl::famus::isMustFlyTask(m_task.get()))
    {
        auto famusTask = std::static_pointer_cast<afrl::famus::MustFlyTask>(m_task);
        if(famusTask->getEnforceHeading())
        {
            auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
            auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
            pTaskOptionClass->m_taskOption->setTaskID(m_mustFlyTask->getTaskID());
            pTaskOptionClass->m_taskOption->setOptionID(optionId);
            pTaskOptionClass->m_taskOption->setCost(1);
            pTaskOptionClass->m_taskOption->setStartLocation(m_mustFlyTask->getPosition()->clone());
            pTaskOptionClass->m_taskOption->setStartHeading(famusTask->getHeading());
            pTaskOptionClass->m_taskOption->setEndLocation(m_mustFlyTask->getPosition()->clone());
            pTaskOptionClass->m_taskOption->setEndHeading(famusTask->getHeading());
            pTaskOptionClass->m_taskOption->getEligibleEntities() = m_mustFlyTask->getEligibleEntities();
            m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
            m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());
            std::string singleOption = "p" + std::to_string(optionId) + " ";
            m_taskPlanOptions->setComposition(singleOption);
            sendSharedLmcpObjectBroadcastMessage(m_taskPlanOptions);
            return;
        }
    }
#endif

    double wedgeDirectionIncrement(n_Const::c_Convert::dPiO8());
    double dHeadingCurrent_rad = 0.0;
    double dHeadingTarget_rad = n_Const::c_Convert::dTwoPi() - wedgeDirectionIncrement;
    while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
    {     
        auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
        auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
        pTaskOptionClass->m_taskOption->setTaskID(m_mustFlyTask->getTaskID());
        pTaskOptionClass->m_taskOption->setOptionID(optionId);
        pTaskOptionClass->m_taskOption->setCost(1);
        pTaskOptionClass->m_taskOption->setStartLocation(m_mustFlyTask->getPosition()->clone());
        pTaskOptionClass->m_taskOption->setStartHeading(dHeadingCurrent_rad * n_Const::c_Convert::dRadiansToDegrees());
        pTaskOptionClass->m_taskOption->setEndLocation(m_mustFlyTask->getPosition()->clone());
        pTaskOptionClass->m_taskOption->setEndHeading(dHeadingCurrent_rad * n_Const::c_Convert::dRadiansToDegrees());
        pTaskOptionClass->m_taskOption->getEligibleEntities() = m_mustFlyTask->getEligibleEntities();
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
        m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());

        optionId++;
        dHeadingCurrent_rad += wedgeDirectionIncrement;
    }


    std::string compositionString("+(");

    for (auto itOption = m_taskPlanOptions->getOptions().begin(); itOption != m_taskPlanOptions->getOptions().end(); itOption++)
    {
        compositionString += "p";
        compositionString += std::to_string((*itOption)->getOptionID());
        compositionString += " ";
    } //for(auto itEligibleEntities=m_speedAltitudeVsEligibleEntitesRequested.begin();itEl ... 

    compositionString += ")";

    m_taskPlanOptions->setComposition(compositionString);

    auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
    sendSharedLmcpObjectBroadcastMessage(newResponse);
}

bool MustFlyTaskService::isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
    std::shared_ptr<TaskOptionClass>& taskOptionClass,
    int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route)
{
    // make sure altitude matches must fly altitude
    auto mustfly = std::dynamic_pointer_cast<afrl::cmasi::MustFlyTask>(m_task);
    for(auto wp : taskImplementationResponse->getTaskWaypoints())
    {
        wp->setAltitude(mustfly->getPosition()->getAltitude());
        wp->setAltitudeType(mustfly->getPosition()->getAltitudeType());
    }

#ifdef AFRL_INTERNAL_ENABLED
    // override speed as necessary
    if(afrl::famus::isMustFlyTask(m_task.get()))
    {
        auto famusTask = std::static_pointer_cast<afrl::famus::MustFlyTask>(m_task);
        if(famusTask->getDesiredSpeed() > 1e-4)
            for(auto wp : taskImplementationResponse->getTaskWaypoints())
                wp->setSpeed(famusTask->getDesiredSpeed());
        return true;
    }
#endif

    return false;
}

bool MustFlyTaskService::isBuildAndSendImplementationRouteRequest(const int64_t& optionId,
    const std::shared_ptr<uxas::messages::task::TaskImplementationRequest>& taskImplementationRequest,
    const std::shared_ptr<uxas::messages::task::TaskOption>& taskOption)
{
    // don't use any of the original planning headings, plan with end heading free
    auto itTaskOptionClass = m_optionIdVsTaskOptionClass.find(optionId);
    if (itTaskOptionClass == m_optionIdVsTaskOptionClass.end())
        return false;

    // set end heading as bearing in case route planner doesn't honor free end heading
    uxas::common::utilities::FlatEarth flatEarth;
    flatEarth.Initialize(taskImplementationRequest->getStartPosition()->getLatitude()*n_Const::c_Convert::dDegreesToRadians(),
                         taskImplementationRequest->getStartPosition()->getLongitude()*n_Const::c_Convert::dDegreesToRadians());
    double north, east;
    flatEarth.ConvertLatLong_degToNorthEast_m(taskOption->getStartLocation()->getLatitude(),
                taskOption->getStartLocation()->getLongitude(), north, east);
    double bearing = atan2(east,north)*n_Const::c_Convert::dRadiansToDegrees();

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
    routeConstraints->setEndLocation(taskOption->getStartLocation()->clone());
    routeConstraints->setEndHeading(bearing);
    routeConstraints->setUseEndHeading(false);

#ifdef AFRL_INTERNAL_ENABLED
    // override heading if required
    if(afrl::famus::isMustFlyTask(m_task.get()))
    {
        auto famusTask = std::static_pointer_cast<afrl::famus::MustFlyTask>(m_task);
        if(famusTask->getEnforceHeading())
        {
            routeConstraints->setEndHeading(famusTask->getHeading());
            routeConstraints->setUseEndHeading(true);
        }
    }
#endif

    routePlanRequest->getRouteRequests().push_back(routeConstraints);

    m_routeIdVsTaskImplementationRequest[routePlanRequest->getRequestID()] = taskImplementationRequest;
    sendSharedLmcpObjectBroadcastMessage(routePlanRequest);

    return true;
}

}; //namespace task
}; //namespace service
}; //namespace uxas

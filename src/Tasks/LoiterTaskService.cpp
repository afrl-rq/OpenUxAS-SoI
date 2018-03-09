// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
 * File:   LoiterTaskService.cpp
 * Author: colin
 *
 * Created on May 4, 2017
 */


#include "LoiterTaskService.h"

#include "Position.h"
#include "FileSystemUtilities.h"
#include "Polygon.h"

#include "afrl/cmasi/Circle.h"
#include "uxas/messages/task/SensorFootprintResponse.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/ROUTE.h"

#include <sstream>      //std::stringstream
#include <iomanip>  //setfill
#include "afrl/cmasi/LoiterAction.h"



namespace uxas {
namespace service {
namespace task {
    
LoiterTaskService::ServiceBase::CreationRegistrar<LoiterTaskService>
LoiterTaskService::s_registrar(LoiterTaskService::s_registryServiceTypeNames());

LoiterTaskService::LoiterTaskService()
: TaskServiceBase(LoiterTaskService::s_typeName(), LoiterTaskService::s_directoryName()) {
};

LoiterTaskService::~LoiterTaskService() {
};

bool
LoiterTaskService::configureTask(const pugi::xml_node& ndComponent) {
    bool isSuccessful(true);

    if (isSuccessful) {
        if (afrl::cmasi::isLoiterTask(m_task.get())) {
            m_loiterTask = std::static_pointer_cast<afrl::cmasi::LoiterTask>(m_task);
            if (m_loiterTask) {

            } else {
                UXAS_LOG_ERROR("ERROR:: **LoiterTaskService::bConfigure failed to cast a AreaSearchTask from the task pointer.");
                isSuccessful = false;
            }
        } else {
            UXAS_LOG_ERROR("**LoiterTaskService::bConfigure failed: taskObject[" + m_task->getFullLmcpTypeName() + "] is not a AngledAreaSearchTask.");
            isSuccessful = false;
        }
    } //isSuccessful
    addSubscriptionAddress(uxas::messages::route::RouteResponse::Subscription);
    return (isSuccessful);
}

bool
LoiterTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) {
    return (false); // always false implies never terminating service from here
};

void LoiterTaskService::buildTaskPlanOptions() {
    int64_t optionId = TaskOptionClass::m_firstOptionId;



    auto taskOption = new uxas::messages::task::TaskOption;
    taskOption->setTaskID(m_loiterTask->getTaskID());
    taskOption->setOptionID(optionId);
    taskOption->getEligibleEntities() = m_loiterTask->getEligibleEntities();
    taskOption->setStartLocation(m_loiterTask->getDesiredAction()->getLocation()->clone());
    //taskOption->setStartHeading(m_watchedEntityStateLast->getHeading());
    taskOption->setEndLocation(m_loiterTask->getDesiredAction()->getLocation()->clone());
    //taskOption->setEndHeading(m_watchedEntityStateLast->getHeading());
    auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
    m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
    m_taskPlanOptions->getOptions().push_back(taskOption);
    taskOption = nullptr; //just gave up ownership

    std::string compositionString("+(");

    for (auto itOption = m_taskPlanOptions->getOptions().begin(); itOption != m_taskPlanOptions->getOptions().end(); itOption++) {
        compositionString += "p";
        compositionString += std::to_string((*itOption)->getOptionID());
        compositionString += " ";
    }

    compositionString += ")";

    m_taskPlanOptions->setComposition(compositionString);

    auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
    sendSharedLmcpObjectBroadcastMessage(newResponse);
};

bool LoiterTaskService::isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
        std::shared_ptr<TaskOptionClass>& taskOptionClass,
        int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route) {

    if (m_loiterTask->getDesiredAction()) {
        auto loiterAction = m_loiterTask->getDesiredAction()->clone();
        if (m_entityStates.find(taskImplementationResponse.get()->getVehicleID()) != m_entityStates.end()) {
            auto state = m_entityStates.find(taskImplementationResponse.get()->getVehicleID())->second;

            loiterAction->getLocation()->setAltitude(state->getLocation()->getAltitude());
            taskImplementationResponse.get()->getTaskWaypoints().back()->getVehicleActionList().push_back(loiterAction);
        }
    }

    return false;
}

void LoiterTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) {

}


}; //namespace task
}; //namespace service
}; //namespace uxas

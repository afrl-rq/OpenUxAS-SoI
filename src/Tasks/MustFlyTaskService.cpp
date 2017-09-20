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

#include "afrl/cmasi/Circle.h"
#include "uxas/messages/task/SensorFootprintResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/ROUTE.h"

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
    : TaskServiceBase(MustFlyTaskService::s_typeName(), MustFlyTaskService::s_directoryName())
{
};

MustFlyTaskService::~MustFlyTaskService()
{
};

bool
MustFlyTaskService::configureTask(const pugi::xml_node& ndComponent)
{
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::cmasi::isMustFlyTask(m_task.get()))
        {
            m_mustFlyTask = std::static_pointer_cast<afrl::cmasi::MustFlyTask>(m_task);
            if (m_mustFlyTask)
            {
            }
            else
            {
                UXAS_LOG_ERROR("**MustFlyTaskService::bConfigure failed to cast a AreaSearchTask from the task pointer.");
                isSuccessful = false;
            }
        }
        else
        {
            UXAS_LOG_ERROR("ERROR:: **MustFlyTaskService::bConfigure failed: taskObject[" + m_task->getFullLmcpTypeName() + "] is not a AngledAreaSearchTask.");
            isSuccessful = false;
        }
    } //isSuccessful
    addSubscriptionAddress(uxas::messages::route::RouteResponse::Subscription);
    return (isSuccessful);
}


bool
MustFlyTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    return (false); // always false implies never terminating service from here
};

void MustFlyTaskService::buildTaskPlanOptions()
{
    int64_t optionId = 1;

    double wedgeDirectionIncrement(n_Const::c_Convert::dPiO8());
    double dHeadingCurrent_rad = 0.0;
    double dHeadingTarget_rad = n_Const::c_Convert::dTwoPi() - wedgeDirectionIncrement;
    while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
    {
        auto taskOption = new uxas::messages::task::TaskOption;
        taskOption->setEndHeading(dHeadingCurrent_rad * n_Const::c_Convert::dRadiansToDegrees());
        taskOption->setStartHeading(dHeadingCurrent_rad * n_Const::c_Convert::dRadiansToDegrees());

        taskOption->setTaskID(m_mustFlyTask->getTaskID());
        taskOption->setOptionID(optionId);
        taskOption->getEligibleEntities() = m_mustFlyTask->getEligibleEntities();
        taskOption->setStartLocation(m_mustFlyTask->getPosition()->clone());
        taskOption->setEndLocation(m_mustFlyTask->getPosition()->clone());
        auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
        m_taskPlanOptions->getOptions().push_back(taskOption);
        taskOption = nullptr; //just gave up ownership

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
};


void MustFlyTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
}
}; //namespace task
}; //namespace service
}; //namespace uxas

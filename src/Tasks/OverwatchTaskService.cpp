// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_WatchTask.cpp
 * Author: steve
 * 
 * Created on February 24, 2016, 6:17 PM
 */


#include "OverwatchTaskService.h"

#include "Position.h"
#include "UnitConversions.h"

#include "avtas/lmcp/LmcpXMLReader.h"
#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/LoiterAction.h"
#include "uxas/messages/task/TaskOption.h"


#include <sstream>      //std::stringstream
#include "afrl/cmasi/GimbalConfiguration.h"


namespace uxas
{
namespace service
{
namespace task
{
OverwatchTaskService::ServiceBase::CreationRegistrar<OverwatchTaskService>
OverwatchTaskService::s_registrar(OverwatchTaskService::s_registryServiceTypeNames());

OverwatchTaskService::OverwatchTaskService()
: DynamicTaskServiceBase(OverwatchTaskService::s_typeName(), OverwatchTaskService::s_directoryName())
{
};

OverwatchTaskService::~OverwatchTaskService()
{
};

bool
OverwatchTaskService::configureDynamicTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isWatchTask(m_task.get()))
        {
            m_watchTask = std::static_pointer_cast<afrl::impact::WatchTask>(m_task);
            if (!m_watchTask)
            {
                UXAS_LOG_ERROR("**OverwatchTaskService::bConfigure failed to cast a WatchTask from the task pointer.");
                isSuccessful = false;
            }
        }
        else
        {
            UXAS_LOG_ERROR("**OverwatchTaskService::bConfigure failed: taskObject[" + m_task->getFullLmcpTypeName() + "] is not a WatchTask.");
            isSuccessful = false;
        }
    } //isSuccessful

    if (m_entityStates.find(m_watchTask->getWatchedEntityID()) != m_entityStates.end())
    {
        m_watchedEntityStateLast = m_entityStates[m_watchTask->getWatchedEntityID()];
    }
    else
    {
        UXAS_LOG_ERROR("Overwatch Task ", m_watchTask->getTaskID(), " Watched Entity ID ", m_watchTask->getWatchedEntityID(), " Does Not Exist");
        isSuccessful = false;
    }

    return (isSuccessful);
}

bool
OverwatchTaskService::processRecievedLmcpMessageDynamicTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpObject);
    if (entityState)
    {
        if (entityState->getID() == m_watchTask->getWatchedEntityID())
        {
            m_watchedEntityStateLast = entityState;
        }
    }
    int64_t optionId(TaskOptionClass::m_firstOptionId);

    return (false); // always false implies never terminating service from here
};


std::shared_ptr<afrl::cmasi::Location3D> OverwatchTaskService::calculateTargetLocation(const std::shared_ptr<afrl::cmasi::EntityState> entityState)
{
    if (m_watchedEntityStateLast)
    {
        return std::make_shared<afrl::cmasi::Location3D>(*m_watchedEntityStateLast->getLocation()->clone());
    }
    return nullptr;
}

}; //namespace task
}; //namespace service
}; //namespace uxas

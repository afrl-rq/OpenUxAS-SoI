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
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RouteResponse.h"
#include "uxas/messages/route/RouteConstraints.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <afrl/cmasi/GimbalConfiguration.h>

#define STRING_XML_ENTITY_STATES "EntityStates" //TODO:: define this in some global place

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "CMPS-CMPS-CMPS-CMPS:: WatchTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "CMPS-CMPS-CMPS-CMPS:: WatchTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
OverwatchTaskService::ServiceBase::CreationRegistrar<OverwatchTaskService>
OverwatchTaskService::s_registrar(OverwatchTaskService::s_registryServiceTypeNames());

OverwatchTaskService::OverwatchTaskService()
: TaskServiceBase(OverwatchTaskService::s_typeName(), OverwatchTaskService::s_directoryName())
{
};

OverwatchTaskService::~OverwatchTaskService()
{
	m_isMakeTransitionWaypointsActive = true;
};

bool
OverwatchTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isWatchTask(m_task.get()))
        {
            m_watchTask = std::static_pointer_cast<afrl::impact::WatchTask>(m_task);
            if (!m_watchTask)
            {
                sstrErrors << "ERROR:: **OverwatchTaskService::bConfigure failed to cast a WatchTask from the task pointer." << std::endl;
                CERR_FILE_LINE_MSG(sstrErrors.str())
                isSuccessful = false;
            }
        }
        else
        {
            sstrErrors << "ERROR:: **OverwatchTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a WatchTask." << std::endl;
            CERR_FILE_LINE_MSG(sstrErrors.str())
            isSuccessful = false;
        }
    } //isSuccessful
    if (isSuccessful)
    {
		if (m_entityStates.find(m_watchTask->getWatchedEntityID()) != m_entityStates.end())
		{
			m_watchedEntityStateLast = m_entityStates[m_watchTask->getWatchedEntityID()];
		}
    } //if(isSuccessful)
    return (isSuccessful);
}

bool
OverwatchTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
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
    return (false); // always false implies never terminating service from here
};

void OverwatchTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

    int64_t optionId(1);
    int64_t taskId(m_watchTask->getTaskID());

    if (isCalculateOption(taskId, optionId, m_watchTask->getEligibleEntities()))
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

bool OverwatchTaskService::isCalculateOption(const int64_t& taskId, int64_t& optionId, const std::vector<int64_t>& eligibleEntities) {
    bool isSuccessful{true};

    if (m_watchedEntityStateLast)
    {
        auto taskOption = new uxas::messages::task::TaskOption;
        taskOption->setTaskID(taskId);
        taskOption->setOptionID(optionId);
        taskOption->getEligibleEntities() = eligibleEntities;
        taskOption->setStartLocation(m_watchedEntityStateLast->getLocation()->clone());
        taskOption->setStartHeading(m_watchedEntityStateLast->getHeading());
        taskOption->setEndLocation(m_watchedEntityStateLast->getLocation()->clone());
        taskOption->setEndHeading(m_watchedEntityStateLast->getHeading());
        auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
        m_taskPlanOptions->getOptions().push_back(taskOption);
        taskOption = nullptr; //just gave up ownership

    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no watchedEntityState found for Entity[" << m_watchTask->getWatchedEntityID() << "]")
        isSuccessful = false;
    }

    return (isSuccessful);
}

void OverwatchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) {
    if (m_watchedEntityStateLast)
    {
        // point the camera at the search point
        auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
        //vehicleActionCommand->setCommandID();
        vehicleActionCommand->setVehicleID(entityState->getID());
        //vehicleActionCommand->setStatus();
		auto gimbalStareAction = std::make_shared<afrl::cmasi::GimbalStareAction>();
        gimbalStareAction->setStarepoint(m_watchedEntityStateLast->getLocation()->clone());
        vehicleActionCommand->getVehicleActionList().push_back(gimbalStareAction->clone());
		if (m_entityConfigurations.find(entityState->getID()) != m_entityConfigurations.end())
		{
			auto config = m_entityConfigurations[entityState->getID()];
			for (auto payload : config->getPayloadConfigurationList())
			{
				if (afrl::cmasi::isGimbalConfiguration(payload))
				{
					gimbalStareAction->setPayloadID(payload->getPayloadID());
				}
			}
		}
        // add the loiter
        auto loiterAction = new afrl::cmasi::LoiterAction();
        loiterAction->setLocation(m_watchedEntityStateLast->getLocation()->clone());
		if (loiterAction->getLocation()->getAltitude() < 5) //too close to ground
		{
			//use current entityStates altitude
			loiterAction->getLocation()->setAltitude(entityState->getLocation()->getAltitude());
		}
        if (m_entityConfigurations.find(entityState->getID()) != m_entityConfigurations.end())
        {
            loiterAction->setAirspeed(m_entityConfigurations[entityState->getID()]->getNominalSpeed());
        }
        else
        {
            CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no EntityConfiguration found for Entity[" << entityState->getID() << "]")
        }
        loiterAction->setRadius(m_loiterRadius_m);
        loiterAction->setAxis(0.0);
        loiterAction->setDirection(afrl::cmasi::LoiterDirection::Clockwise);
        loiterAction->setDuration(-1.0);
        loiterAction->setLength(0.0);
        loiterAction->setLoiterType(afrl::cmasi::LoiterType::Circular);
        vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
        loiterAction = nullptr; //gave up ownership

        // send out the response
        auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(vehicleActionCommand);
        sendSharedLmcpObjectBroadcastMessage(newMessage);
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no watchedEntityState found for Entity[" << m_watchTask->getWatchedEntityID() << "]")
    }
}


}; //namespace task
}; //namespace service
}; //namespace uxas

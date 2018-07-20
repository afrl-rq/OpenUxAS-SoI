// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_TaskManager.cpp
 * Author: steve
 * 
 * Created on August 31, 2015, 6:17 PM
 */


#include "TaskManagerService.h"
#include "TaskServiceBase.h"


#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityConfigurationDescendants.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/EntityStateDescendants.h"
#include "afrl/cmasi/AutomationRequest.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/TaskDescendants.h"
#include "afrl/cmasi/RemoveTasks.h"
#include "afrl/cmasi/FollowPathCommand.h"
#include "uxas/messages/uxnative/CreateNewService.h"
#include "uxas/messages/uxnative/KillService.h"
#include "avtas/lmcp/LmcpXMLReader.h"
#include "afrl/cmasi/FollowPathCommand.h"      

#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"



#include "pugixml.hpp"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <fstream>     // std::ifstream
#include <cstdint>
#include <memory>      //int64_t


#define STRING_XML_TYPE "Type"
#define STRING_XML_TASKOPTIONS "TaskOptions"
#define STRING_XML_TASKID "TaskId"
#define STRING_XML_TASKTYPE "TaskType"
#define STRING_XML_OPTION "Option"
#define STRING_XML_OPTIONNAME "OptionName"
#define STRING_XML_VALUE "Value"

#define COUT_INFO_MSG(MESSAGE) std::cout << "<>TaskManager::" << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>TaskManager::" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>TaskManager::" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
TaskManagerService::ServiceBase::CreationRegistrar<TaskManagerService>
TaskManagerService::s_registrar(TaskManagerService::s_registryServiceTypeNames());

TaskManagerService::TaskManagerService()
    : ServiceBase(TaskManagerService::s_typeName(), TaskManagerService::s_directoryName())
{
}

TaskManagerService::~TaskManagerService() { };

bool
TaskManagerService::configure(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    std::stringstream sstrErrors;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();
    //assert(strComponentType==STRING_XML_COMPONENT_TYPE)

    for (pugi::xml_node ndCurrent = ndComponent.first_child(); ndCurrent; ndCurrent = ndCurrent.next_sibling())
    {
        if (std::string(STRING_XML_TASKOPTIONS) == ndCurrent.name())
        {
            int64_t taskId = 0;
            std::string taskType = m_noTaskTypeString;
            if (!ndCurrent.attribute(STRING_XML_TASKID).empty())
            {
                taskId = ndCurrent.attribute(STRING_XML_TASKID).as_int64();
            }
            else if (!ndCurrent.attribute(STRING_XML_TASKTYPE).empty()) // only use type is there is no taskid
            {
                taskType = ndCurrent.attribute(STRING_XML_TASKTYPE).value();
            }

            std::string taskOptions;

            for (pugi::xml_node ndOption = ndCurrent.first_child(); ndOption; ndOption = ndOption.next_sibling())
            {
                if (std::string(STRING_XML_OPTION) == ndOption.name())
                {
                    if (!ndOption.attribute(STRING_XML_OPTIONNAME).empty())
                    {
                        std::string optionName = ndOption.attribute(STRING_XML_OPTIONNAME).value();
                        std::string value; // value is not required
                        if (!ndOption.attribute(STRING_XML_VALUE).empty())
                        {
                            value = ndOption.attribute(STRING_XML_VALUE).value();
                            taskOptions += "<" + optionName + ">" + value + "</" + optionName + ">";
                        }
                        else
                        {
                            taskOptions += "<" + optionName + "/>";
                        }
                    }
                }
            }
            if (!taskOptions.empty())
            {
                m_TaskIdVsTaskTypeVsOptions[taskId][taskType].push_back(taskOptions);
            }
        } //                    if (std::string(STRING_XML_SUBSCRIBE_TO_MESSAGES) == ndCurrent.name())
    } //for (pugi::xml_node ndCurrent = ndConfigurationEntries.first_child(); ndCurrent; ndCurrent = ndCurrent.next_sibling())

    addSubscriptionAddress(afrl::cmasi::RemoveTasks::Subscription);
    
    //ENTITY CONFIGURATIONS
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
    for(auto child : childconfigs)
        addSubscriptionAddress(child);
    
    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);

    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    addSubscriptionAddress(afrl::cmasi::FollowPathCommand::Subscription);

    addSubscriptionAddress(afrl::impact::AreaOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::LineOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::PointOfInterest::Subscription);
    
    // Subscribe to Task and all derivatives of Task
    addSubscriptionAddress(afrl::cmasi::Task::Subscription);
    std::vector< std::string > childtasks = afrl::cmasi::TaskDescendants();
    for(auto child : childtasks)
        addSubscriptionAddress(child);

    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::OperatingRegion::Subscription);

    return true;
}

bool
TaskManagerService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    std::shared_ptr<avtas::lmcp::Object> messageObject = receivedLmcpMessage->m_object;
    std::stringstream sstrError;

    auto baseTask = std::dynamic_pointer_cast<afrl::cmasi::Task>(messageObject);
    auto entityConfiguration = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(messageObject);
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(messageObject);

    if (baseTask)
    {
        bool isGoodTask = true;

        int64_t taskId = baseTask->getTaskID();

        auto itServiceId = m_TaskIdVsServiceId.find(taskId);
        if (itServiceId != m_TaskIdVsServiceId.end())
        {
            // kill the current service
            auto killServiceMessage = std::make_shared<uxas::messages::uxnative::KillService>();
            killServiceMessage->setServiceID(itServiceId->second);
            auto message = std::static_pointer_cast<avtas::lmcp::Object>(killServiceMessage);
            sendSharedLmcpObjectBroadcastMessage(message);
            m_TaskIdVsServiceId.erase(itServiceId);
            UXAS_LOG_WARN("taskID ", taskId, " already exists. Killing previous task");
        }
        //COUT_INFO_MSG("Adding Task[" << taskId << "]")

        std::string taskOptions;

        // FIRST CHECK FOR GLOBAL OPTIONS
        auto itTaskTypeVsOptions = m_TaskIdVsTaskTypeVsOptions.find(0);
        if (itTaskTypeVsOptions != m_TaskIdVsTaskTypeVsOptions.end())
        {
            auto itOptions = itTaskTypeVsOptions->second.find(m_noTaskTypeString);
            if (itOptions != itTaskTypeVsOptions->second.end())
            {
                for (auto& option : itOptions->second)
                {
                    taskOptions += option;
                }
            }
        }

        // NEXT CHECK SPECIFIC OPTIONS 
        itTaskTypeVsOptions = m_TaskIdVsTaskTypeVsOptions.find(taskId);
        if (itTaskTypeVsOptions != m_TaskIdVsTaskTypeVsOptions.end())
        {
            auto itOptions = itTaskTypeVsOptions->second.find(m_noTaskTypeString);
            if (itOptions != itTaskTypeVsOptions->second.end())
            {
                for (auto& option : itOptions->second)
                {
                    taskOptions += option;
                }
            }
        }
        else //if(itTaskTypeVsOptions != m_TaskIdVsTaskTypeVsOptions.end())
        {
            auto itTaskTypeVsOptions = m_TaskIdVsTaskTypeVsOptions.find(0);
            if (itTaskTypeVsOptions != m_TaskIdVsTaskTypeVsOptions.end())
            {
                auto itOptions = itTaskTypeVsOptions->second.find(baseTask->getFullLmcpTypeName());
                if (itOptions != itTaskTypeVsOptions->second.end())
                {
                    for (auto& option : itOptions->second)
                    {
                        taskOptions += option;
                    }
                }
            }
        } //if(itTaskTypeVsOptions != m_TaskIdVsTaskTypeVsOptions.end())

        std::string xmlTaskOptions;
        if (!taskOptions.empty())
        {
            xmlTaskOptions = "<" + TaskServiceBase::m_taskOptions_XmlTag + ">" + taskOptions + "</" + TaskServiceBase::m_taskOptions_XmlTag + ">";
            //COUT_INFO_MSG("INFO:: TaskId[" << taskId << "] xmlTaskOptions[" << xmlTaskOptions << "]")
        }

        auto createNewServiceMessage = std::make_shared<uxas::messages::uxnative::CreateNewService>();
        auto serviceId = ServiceBase::getUniqueServceId();
        createNewServiceMessage->setServiceID(serviceId);
        std::string xmlConfigStr = "<Service Type=\"" + baseTask->getFullLmcpTypeName() + "\">" +
                " <TaskRequest>" + baseTask->toXML() + "</TaskRequest>\n" + xmlTaskOptions;
        uxas::common::StringUtil::ReplaceAll(xmlConfigStr, "<", "&lt;");
        uxas::common::StringUtil::ReplaceAll(xmlConfigStr, ">", "&gt;");
        createNewServiceMessage->setXmlConfiguration(xmlConfigStr);

        // add all existing entities for new service initialization
        for (auto& entityConfiguration : m_idVsEntityConfiguration)
        {
            createNewServiceMessage->getEntityConfigurations().push_back(entityConfiguration.second->clone());
        }
        
        // add all existing entities for new service initialization
        for (auto& entityState : m_idVsEntityState)
        {
            createNewServiceMessage->getEntityStates().push_back(entityState.second->clone());
        }

        for (auto kiz : m_idVsKeepInZone)
        {
          createNewServiceMessage->getKeepInZones().push_back(kiz.second->clone());
        }
        for (auto koz : m_idVsKeepOutZone)
        {
          createNewServiceMessage->getKeepOutZones().push_back(koz.second->clone());
        }
        for (auto opr : m_idVsOperatingRegion)
        {
          createNewServiceMessage->getOperatingRegions().push_back(opr .second->clone());
        }

        // add the appropriate area/line/point of interest if new task requires knowledge of it
        // TODO: simply send all areas/lines/points to all tasks and let each one find the necessary information
        if (afrl::impact::isAngledAreaSearchTask(messageObject.get()))
        {
            auto angledAreaSearchTask = std::static_pointer_cast<afrl::impact::AngledAreaSearchTask>(messageObject);
            auto itAreaOfInterest = m_idVsAreaOfInterest.find(angledAreaSearchTask->getSearchAreaID());
            if (itAreaOfInterest != m_idVsAreaOfInterest.end())
            {
                createNewServiceMessage->getAreas().push_back(itAreaOfInterest->second->clone());
            }
            else
            {
                isGoodTask = false;
                CERR_FILE_LINE_MSG("ERROR:: could not find SearchArea[" << angledAreaSearchTask->getSearchAreaID()
                                   << "] for requested AngledAreaSearchTask[" << taskId << "]")
            }
        }
        else if (afrl::impact::isImpactLineSearchTask(messageObject.get()))
        {
            auto impactLineSearchTask = std::static_pointer_cast<afrl::impact::ImpactLineSearchTask>(messageObject);
            auto itLine = m_idVsLineOfInterest.find(impactLineSearchTask->getLineID());
            if (itLine != m_idVsLineOfInterest.end())
            {
                createNewServiceMessage->getLines().push_back(itLine->second->clone());
            }
            else
            {
                isGoodTask = false;
                CERR_FILE_LINE_MSG("ERROR:: could not find Line[" << impactLineSearchTask->getLineID()
                                   << "] for requested ImpactLineSearchTask[" << taskId << "]")
            }
        }
        else if (afrl::impact::isImpactPointSearchTask(messageObject.get()))
        {
            auto impactPointSearchTask = std::static_pointer_cast<afrl::impact::ImpactPointSearchTask>(messageObject);
            if (impactPointSearchTask->getSearchLocationID() > 0)
            {
                auto itPoint = m_idVsPointOfInterest.find(impactPointSearchTask->getSearchLocationID());
                if (itPoint != m_idVsPointOfInterest.end())
                {
                    createNewServiceMessage->getPoints().push_back(itPoint->second->clone());
                }
                else
                {
                    isGoodTask = false;
                    CERR_FILE_LINE_MSG("ERROR:: could not find SearchLocation[" << impactPointSearchTask->getSearchLocationID()
                                       << "] for requested ImpactPointSearchTask[" << taskId << "]")
                }
            }
        }
        else if (afrl::impact::isPatternSearchTask(messageObject.get()))
        {
            auto patternSearchTask = std::static_pointer_cast<afrl::impact::PatternSearchTask>(messageObject);
            if (patternSearchTask->getSearchLocationID() > 0)
            {
                auto itPoint = m_idVsPointOfInterest.find(patternSearchTask->getSearchLocationID());
                if (itPoint != m_idVsPointOfInterest.end())
                {
                    createNewServiceMessage->getPoints().push_back(itPoint->second->clone());
                }
                else
                {
                    isGoodTask = false;
                    CERR_FILE_LINE_MSG("ERROR:: could not find SearchLocation[" << patternSearchTask->getSearchLocationID()
                                       << "] for requested PatternSearchTask[" << taskId << "]")
                }
            }
        }
        else if (afrl::impact::isEscortTask(messageObject.get()))
        {
            // escort attempts to determine 'supported entity' route from all lines of interest or mission commands
            for (auto line : m_idVsLineOfInterest)
            {
                createNewServiceMessage->getLines().push_back(line.second->clone());
            }
            for (auto missionCommand : m_vehicleIdVsCurrentMission)
            {
                createNewServiceMessage->getMissionCommands().push_back(missionCommand.second->clone());
            }
        }

        if (isGoodTask)
        {
            m_TaskIdVsServiceId[taskId] = serviceId;
            auto newServiceMessage = std::static_pointer_cast<avtas::lmcp::Object>(createNewServiceMessage);
            sendSharedLmcpObjectBroadcastMessage(newServiceMessage);
            //CERR_FILE_LINE_MSG("Added Task[" << taskId << "]")
        }
    }
    else if (entityConfiguration)
    {
        m_idVsEntityConfiguration[entityConfiguration->getID()] = entityConfiguration;
    }
    else if (entityState)
    {
        m_idVsEntityState[entityState->getID()] = entityState;
    }
    else if (afrl::impact::isAreaOfInterest(messageObject.get()))
    {
        auto areaOfInterest = std::static_pointer_cast<afrl::impact::AreaOfInterest>(messageObject);
        m_idVsAreaOfInterest[areaOfInterest->getAreaID()] = areaOfInterest;
    }
    else if (afrl::impact::isLineOfInterest(messageObject.get()))
    {
        auto lineOfInterest = std::static_pointer_cast<afrl::impact::LineOfInterest>(messageObject);
        m_idVsLineOfInterest[lineOfInterest->getLineID()] = lineOfInterest;
    }
    else if (afrl::impact::isPointOfInterest(messageObject.get()))
    {
        auto pointOfInterest = std::static_pointer_cast<afrl::impact::PointOfInterest>(messageObject);
        m_idVsPointOfInterest[pointOfInterest->getPointID()] = pointOfInterest;
    }
    else if (afrl::cmasi::isAutomationRequest(messageObject.get()))
    {
        auto automationRequest = std::static_pointer_cast<afrl::cmasi::AutomationRequest>(messageObject);
        auto uniqueAutomationRequest = std::make_shared<uxas::messages::task::UniqueAutomationRequest>();
        uniqueAutomationRequest->setOriginalRequest(automationRequest->clone());
        uniqueAutomationRequest->setRequestID(m_automationRequestId);
        m_automationRequestId++;
        auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(uniqueAutomationRequest);
        sendSharedLmcpObjectBroadcastMessage(newMessage);
    }
    else if (afrl::cmasi::isAutomationResponse(messageObject.get()))
    {
        auto ares = std::static_pointer_cast<afrl::cmasi::AutomationResponse>(messageObject);
        for (auto v : ares->getMissionCommandList())
        {
            m_vehicleIdVsCurrentMission[v->getVehicleID()] = std::shared_ptr<afrl::cmasi::MissionCommand>(v->clone());
        }
    }
    else if (afrl::cmasi::isMissionCommand(messageObject.get()))
    {
        auto mish = std::static_pointer_cast<afrl::cmasi::MissionCommand>(messageObject);
        m_vehicleIdVsCurrentMission[mish->getVehicleID()] = mish;
    }
    else if (afrl::cmasi::isKeepInZone(messageObject.get()))
    {
        auto kiz = std::static_pointer_cast<afrl::cmasi::KeepInZone>(messageObject);
        m_idVsKeepInZone[kiz->getZoneID()] = kiz;
    }
    else if (afrl::cmasi::isKeepOutZone(messageObject.get()))
    {
        auto koz = std::static_pointer_cast<afrl::cmasi::KeepOutZone>(messageObject);
        m_idVsKeepOutZone[koz->getZoneID()] = koz;
    }
    else if (afrl::cmasi::isOperatingRegion(messageObject.get()))
    {
        auto opr = std::static_pointer_cast<afrl::cmasi::OperatingRegion>(messageObject);
        m_idVsOperatingRegion[opr ->getID()] = opr ;
    }
    else if (afrl::cmasi::isFollowPathCommand(messageObject.get()))
    {
        auto fpc = std::static_pointer_cast<afrl::cmasi::FollowPathCommand>(messageObject);
        auto path = std::shared_ptr<afrl::cmasi::MissionCommand>(new afrl::cmasi::MissionCommand);
        for (auto wp : fpc->getWaypointList())
        {
            path->getWaypointList().push_back(wp->clone());
        }
        m_vehicleIdVsCurrentMission[fpc->getVehicleID()] = path;
    }
    else if (afrl::cmasi::isRemoveTasks(messageObject.get()))
    {
        auto removeTasks = std::static_pointer_cast<afrl::cmasi::RemoveTasks>(messageObject);
        auto countBefore = m_TaskIdVsServiceId.size();
        for (auto itTaskId = removeTasks->getTaskList().begin(); itTaskId != removeTasks->getTaskList().end(); itTaskId++)
        {
                auto itServiceId = m_TaskIdVsServiceId.find(*itTaskId);
                if (itServiceId != m_TaskIdVsServiceId.end())
                {
                    // kill the current service
                    auto killServiceMessage = std::make_shared<uxas::messages::uxnative::KillService>();
                    killServiceMessage->setServiceID(itServiceId->second);
                    auto message = std::static_pointer_cast<avtas::lmcp::Object>(killServiceMessage);
                    sendSharedLmcpObjectBroadcastMessage(message);
                    m_TaskIdVsServiceId.erase(itServiceId);
                    UXAS_LOG_INFORM("Removed Task[" << *itTaskId << "]")
                }
                else
                {
                    CERR_FILE_LINE_MSG("ERROR:: Tried to kill service, but could not find ServiceId for TaskId[" << *itTaskId << "]")
                }
        }
        std::string taskList = "[";
        for (auto taskID : removeTasks->getTaskList())
        {
            taskList += std::to_string(taskID) + " ";
        }
        taskList += "]";
        IMPACT_INFORM("Removed ", countBefore - m_TaskIdVsServiceId.size(), " tasks containing ", taskList, ". ", m_TaskIdVsServiceId.size(), " Still Exist.");
    }
    else
    {
        //CERR_FILE_LINE_MSG("WARNING::TaskManagerService::ProcessMessage: MessageType [" << messageObject->getFullLmcpTypeName() << "] not processed.")
    }
    return (false); // always false implies never terminating service from here
};

std::string TaskManagerService::GetTaskStringIdFromId(const int64_t& taskId)
{
    return ("TASK_" + std::to_string(taskId));
}


}; //namespace task
}; //namespace service
}; //namespace uxas

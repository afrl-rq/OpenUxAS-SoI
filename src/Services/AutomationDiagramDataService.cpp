// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_AutomationDiagram.cpp
 * Author: steve
 * 
 * Created on February 1, 2016, 6:17 PM
 */


#include "AutomationDiagramDataService.h"

#include "FileSystemUtilities.h"

#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/EntityStateDescendants.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "afrl/cmasi/CameraConfiguration.h"

#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/TaskDescendants.h"  

#include "uxas/messages/task/SensorFootprintResponse.h"
#include "uxas/messages/task/SensorFootprint.h"

#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"

#include "TimeUtilities.h"
#include "Constants/Convert.h"

#include "pugixml.hpp"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <fstream>     // std::ifstream
#include <cstdint>
#include <memory>      //int64_t
#include <iomanip>      //setfill

#define STRING_COMPONENT_NAME "AutomationDiagram"

#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"

#define COUT_INFO_MSG(MESSAGE) std::cout << "<>AutomationDiagram:" << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>AutomationDiagram::" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>AutomationDiagram:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();

#define MIMIMUM_ASSIGNED_ALTITUDE_M (10.0)    
#define GIMBAL_STEP_SIZE_RAD (5.0*n_Const::c_Convert::dDegreesToRadians())
#define HORIZANTAL_FOV_STEP_SIZE_DEG (5.0)

namespace uxas
{
namespace service
{
namespace data
{
AutomationDiagramDataService::ServiceBase::CreationRegistrar<AutomationDiagramDataService>
AutomationDiagramDataService::s_registrar(AutomationDiagramDataService::s_registryServiceTypeNames());

AutomationDiagramDataService::AutomationDiagramDataService()
: ServiceBase(AutomationDiagramDataService::s_typeName(), AutomationDiagramDataService::s_directoryName()) { };

AutomationDiagramDataService::~AutomationDiagramDataService() { };

bool
AutomationDiagramDataService::configure(const pugi::xml_node& ndComponent)

{
    bool isSuccess{true};

    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    m_basePath = strBasePath;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();
    //assert(strComponentType==STRING_XML_COMPONENT_TYPE)
    
    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);

    //AUTOMATION
    addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::UniqueAutomationResponse::Subscription);

    //BOUNDARIES
    addSubscriptionAddress(afrl::cmasi::OperatingRegion::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);

    //REGION OF INTEREST
    addSubscriptionAddress(afrl::impact::AreaOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::LineOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::PointOfInterest::Subscription);

    addSubscriptionAddress(afrl::impact::AreaOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::LineOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::PointOfInterest::Subscription);
    
    // Subscribe to Task and all derivatives of Task
    addSubscriptionAddress(afrl::cmasi::Task::Subscription);
    std::vector< std::string > childtasks = afrl::cmasi::TaskDescendants();
    for(auto child : childtasks)
        addSubscriptionAddress(child);

    return (isSuccess);
}

bool
AutomationDiagramDataService::initialize()
{
    bool isSuccess{true};
    return (isSuccess);
}

bool
AutomationDiagramDataService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    std::stringstream sstrError;
    bool isMessageProcessed(false);

    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
    if (entityState)
    {
        m_idVsLastEntityState[entityState->getID()] = entityState;
        isMessageProcessed = true;
    }
    if (!isMessageProcessed)
    {
        auto uniqueAutomationRequest = std::dynamic_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage->m_object);
        if (uniqueAutomationRequest)
        {
            m_idVsAutomationRequest[uniqueAutomationRequest->getRequestID()] = uniqueAutomationRequest;
            m_idVsTimeAutomationRequest_ms[uniqueAutomationRequest->getRequestID()] = uxas::common::utilities::c_TimeUtilities::getTimeNow_ms(true);
            isMessageProcessed = true;
        }
    }
    if (!isMessageProcessed)
    {
        auto abstractZone = std::dynamic_pointer_cast<afrl::cmasi::AbstractZone>(receivedLmcpMessage->m_object);
        if (abstractZone)
        {
            m_idVsZone[abstractZone->getZoneID()] = abstractZone;
            isMessageProcessed = true;
        }
    }
    if (!isMessageProcessed)
    {
        auto task = std::dynamic_pointer_cast<afrl::cmasi::Task>(receivedLmcpMessage->m_object);
        if (task)
        {
            m_idVsTask[task->getTaskID()] = task;
            isMessageProcessed = true;
        }
    }
    if (!isMessageProcessed)
    {
        auto operatingRegion = std::dynamic_pointer_cast<afrl::cmasi::OperatingRegion>(receivedLmcpMessage->m_object);
        if (operatingRegion)
        {
            m_idVsOperatingRegion[operatingRegion->getID()] = operatingRegion;
            isMessageProcessed = true;
        }
    }
    if (!isMessageProcessed)
    {
        auto uniqueAutomationResponse = std::dynamic_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(receivedLmcpMessage->m_object);
        if (uniqueAutomationResponse)
        {
            auto itassigmentTime_ms = m_idVsTimeAutomationRequest_ms.find(uniqueAutomationResponse->getResponseID());
            if (itassigmentTime_ms != m_idVsTimeAutomationRequest_ms.end())
            {
                auto assigmentTime_ms = uxas::common::utilities::c_TimeUtilities::getTimeNow_ms(true) - itassigmentTime_ms->second;
                COUT_INFO_MSG("INFO::Total ASSIGNMENT TIME [" << double(assigmentTime_ms) / 1000.0 << "]")
            }
            ProcessUniqueAutomationResponse(uniqueAutomationResponse);
            isMessageProcessed = true;
        }
    }
    if (!isMessageProcessed)
    {
        auto areaOfInterest = std::dynamic_pointer_cast<afrl::impact::AreaOfInterest>(receivedLmcpMessage->m_object);
        if (areaOfInterest)
        {
            m_idVsAreaOfInterest[areaOfInterest->getAreaID()] = areaOfInterest;
            isMessageProcessed = true;
        }
    }
    if (!isMessageProcessed)
    {
        auto lineOfInterest = std::dynamic_pointer_cast<afrl::impact::LineOfInterest>(receivedLmcpMessage->m_object);
        if (lineOfInterest)
        {
            m_idVsLineOfInterest[lineOfInterest->getLineID()] = lineOfInterest;
            isMessageProcessed = true;
        }
    }
    if (!isMessageProcessed)
    {
        auto pointOfInterest = std::dynamic_pointer_cast<afrl::impact::PointOfInterest>(receivedLmcpMessage->m_object);
        if (pointOfInterest)
        {
            m_idVsPointOfInterest[pointOfInterest->getPointID()] = pointOfInterest;
            isMessageProcessed = true;
        }
    }
    if (!isMessageProcessed)
    {
        //        UXAS_LOG_WARN("WARNING::AutomationDiagramDataService::ProcessMessage: MessageType [" 
        //                , receivedLmcpMessage->m_object->getFullLmcpTypeName() 
        //                , "] serviceId[" , m_serviceId
        //                , "] SourceEntityId[" , receivedLmcpMessage->m_attributes->getSourceEntityId()
        //                , "] SourceServiceId[" , receivedLmcpMessage->m_attributes->getSourceServiceId() 
        //                , "] not processed.");
    }
    return (false); // always false implies never terminating service from here
};

void AutomationDiagramDataService::ProcessUniqueAutomationResponse(std::shared_ptr<uxas::messages::task::UniqueAutomationResponse>& uniqueAutomationResponse)
{
    // 1) find the corresponding uniqueautomation request
    auto itUniqueAutomationRequest = m_idVsAutomationRequest.find(uniqueAutomationResponse->getResponseID());
    if (itUniqueAutomationRequest != m_idVsAutomationRequest.end())
    {
        // 2) get directory for saving diagram/files
        std::stringstream sstrErrors;
        std::string savePath;
        std::stringstream sstrNewDirectoryPrefix;
        sstrNewDirectoryPrefix << STRING_COMPONENT_NAME << "_ID" << std::setfill('0') << std::setw(4) << m_entityId;
        std::string strComponentPath = m_basePath + "/";
        bool isSucceeded = uxas::common::utilities::c_FileSystemUtilities::bCreateUniqueDirectory(strComponentPath, sstrNewDirectoryPrefix.str(), savePath, sstrErrors);
        if (isSucceeded)
        {
            // 3) collect all of the tasks, zones, operation regions, entityStates(?),process inputs into files for python, save into directory
            //STATES
            
            // if the 'EntityList' is empty, then ALL vehicles are considered eligible
            if(itUniqueAutomationRequest->second->getOriginalRequest()->getEntityList().empty())
            {
                for(auto entity : m_idVsLastEntityState)
                {
                    itUniqueAutomationRequest->second->getOriginalRequest()->getEntityList().push_back(entity.second->getID());
                }
            }
            
            for (auto& entityId : itUniqueAutomationRequest->second->getOriginalRequest()->getEntityList())
            {
                bool isFoundEntityState{false};

                for (auto& planningState : itUniqueAutomationRequest->second->getPlanningStates())
                {
                    if (planningState->getEntityID() == entityId)
                    {
                        isFoundEntityState = true;

                        auto entityState = new afrl::cmasi::EntityState;
                        entityState->setID(entityId);
                        entityState->setLocation(planningState->getPlanningPosition()->clone());
                        entityState->setHeading(planningState->getPlanningHeading());

                        std::string fileName = savePath + "EntityState_Id_" + std::to_string(entityId) + ".xml";
                        std::ofstream file(fileName);
                        file << entityState->toXML();
                        file.close();

                        delete entityState;
                        break;
                    }
                }
                if (!isFoundEntityState)
                {
                    auto itEntity = m_idVsLastEntityState.find(entityId);
                    if (itEntity != m_idVsLastEntityState.end())
                    {
                        isFoundEntityState = true;
                        std::string fileName = savePath + "EntityState_Id_" + std::to_string(itEntity->second->getID()) + ".xml";
                        std::ofstream file(fileName);
                        file << itEntity->second->toXML();
                        file.close();
                    }
                }
                if (!isFoundEntityState)
                {
                    CERR_FILE_LINE_MSG("ERROR::ProcessUniqueAutomationResponse: entityId[" << entityId << "] not found.")
                }
            }
            //TASKS
            for (auto& taskId : itUniqueAutomationRequest->second->getOriginalRequest()->getTaskList())
            {
                auto itTask = m_idVsTask.find(taskId);
                if (itTask != m_idVsTask.end())
                {
                    std::string fileName = savePath + "Task_Id_" + std::to_string(itTask->second->getTaskID()) + ".xml";
                    std::ofstream file(fileName);
                    file << itTask->second->toXML();
                    file.close();

                    // get the IMPACT REGIONs OF INTEREST
                    auto task = itTask->second;
                    if (afrl::impact::isAngledAreaSearchTask(task.get()))
                    {
                        auto angledAreaSearchTask = std::static_pointer_cast<afrl::impact::AngledAreaSearchTask>(task);
                        assert(angledAreaSearchTask);
                        if (angledAreaSearchTask->getSearchAreaID() > 0)
                        {
                            auto itAreaOfInterest = m_idVsAreaOfInterest.find(angledAreaSearchTask->getSearchAreaID());
                            if (itAreaOfInterest != m_idVsAreaOfInterest.end())
                            {
                                std::string fileName = savePath + "AreaOfInterest_Id_" + std::to_string(angledAreaSearchTask->getSearchAreaID()) + ".xml";
                                std::ofstream file(fileName);
                                file << itAreaOfInterest->second->toXML();
                                file.close();
                            }
                            else
                            {
                                CERR_FILE_LINE_MSG("ERROR::AngledAreaSearchTask: AreaOfInterest [" << angledAreaSearchTask->getSearchAreaID() << "] not found for angledAreaSearchTask [" << angledAreaSearchTask->getTaskID() << "].")
                            }
                        }
                    }
                    else if (afrl::impact::isImpactLineSearchTask(task.get()))
                    {
                        auto impactLineSearchTask = std::static_pointer_cast<afrl::impact::ImpactLineSearchTask>(task);
                        assert(impactLineSearchTask);
                        if (impactLineSearchTask->getLineID() > 0)
                        {
                            auto itLineOfInterest = m_idVsLineOfInterest.find(impactLineSearchTask->getLineID());
                            if (itLineOfInterest != m_idVsLineOfInterest.end())
                            {
                                std::string fileName = savePath + "LineOfInterest_Id_" + std::to_string(impactLineSearchTask->getLineID()) + ".xml";
                                std::ofstream file(fileName);
                                file << itLineOfInterest->second->toXML();
                                file.close();
                            }
                            else
                            {
                                CERR_FILE_LINE_MSG("ERROR::ImpactLineSearchTask: LineOfInterest [" << impactLineSearchTask->getLineID() << "] not found for impactLineSearchTask [" << impactLineSearchTask->getTaskID() << "].")
                            }
                        }
                    }
                    else if (afrl::impact::isImpactPointSearchTask(task.get()))
                    {
                        auto impactPointSearchTask = std::static_pointer_cast<afrl::impact::ImpactPointSearchTask>(task);
                        assert(impactPointSearchTask);
                        if (impactPointSearchTask->getSearchLocationID() > 0)
                        {
                            auto itPointOfInterest = m_idVsPointOfInterest.find(impactPointSearchTask->getSearchLocationID());
                            if (itPointOfInterest != m_idVsPointOfInterest.end())
                            {
                                std::string fileName = savePath + "PointOfInterest_Id_" + std::to_string(impactPointSearchTask->getSearchLocationID()) + ".xml";
                                std::ofstream file(fileName);
                                file << itPointOfInterest->second->toXML();
                                file.close();
                            }
                            else
                            {
                                CERR_FILE_LINE_MSG("ERROR::PatternSearchTask: PointOfInterest [" << impactPointSearchTask->getSearchLocationID() << "] not found for angledAreaSearchTask [" << impactPointSearchTask->getTaskID() << "].")
                            }
                        }
                    }
                    else if (afrl::impact::isPatternSearchTask(task.get()))
                    {
                        auto patternSearchTask = std::static_pointer_cast<afrl::impact::PatternSearchTask>(task);
                        assert(patternSearchTask);
                        if (patternSearchTask->getSearchLocationID() > 0)
                        {
                            auto itPointOfInterest = m_idVsPointOfInterest.find(patternSearchTask->getSearchLocationID());
                            if (itPointOfInterest != m_idVsPointOfInterest.end())
                            {
                                std::string fileName = savePath + "PointOfInterest_Id_" + std::to_string(patternSearchTask->getSearchLocationID()) + ".xml";
                                std::ofstream file(fileName);
                                file << itPointOfInterest->second->toXML();
                                file.close();
                            }
                            else
                            {
                                CERR_FILE_LINE_MSG("ERROR::PatternSearchTask: PointOfInterest [" << patternSearchTask->getSearchLocationID() << "] not found for angledAreaSearchTask [" << patternSearchTask->getTaskID() << "].")
                            }
                        }
                    }
                    else if (afrl::impact::isWatchTask(task.get()))
                    {
                        auto watchTask = std::static_pointer_cast<afrl::impact::WatchTask>(task);
                        assert(watchTask);
                        if (watchTask->getWatchedEntityID() > 0)
                        {
                            auto itWatchedEntity = m_idVsLastEntityState.find(watchTask->getWatchedEntityID());
                            if (itWatchedEntity != m_idVsLastEntityState.end())
                            {
                                std::string fileName = savePath + "WatchedEntity_Id_" + std::to_string(watchTask->getWatchedEntityID()) + ".xml";
                                std::ofstream file(fileName);
                                file << itWatchedEntity->second->toXML();
                                file.close();
                            }
                            else
                            {
                                CERR_FILE_LINE_MSG("ERROR::watchTask: WatchedEntity [" << watchTask->getWatchedEntityID() << "] not found for watchTask [" << watchTask->getTaskID() << "].")
                            }
                        }
                    }
                    else if (afrl::impact::isBlockadeTask(task.get()))
                    {
                        auto blockadeTask = std::static_pointer_cast<afrl::impact::BlockadeTask>(task);
                        assert(blockadeTask);
                        if (blockadeTask->getBlockedEntityID() > 0)
                        {
                            auto itgetBlockedEntity = m_idVsLastEntityState.find(blockadeTask->getBlockedEntityID());
                            if (itgetBlockedEntity != m_idVsLastEntityState.end())
                            {
                                std::string fileName = savePath + "BlockedEntity_Id_" + std::to_string(blockadeTask->getBlockedEntityID()) + ".xml";
                                std::ofstream file(fileName);
                                file << itgetBlockedEntity->second->toXML();
                                file.close();
                            }
                            else
                            {
                                CERR_FILE_LINE_MSG("ERROR::blockadeTask: WatchedEntity [" << blockadeTask->getBlockedEntityID() << "] not found for blockadeTask [" << blockadeTask->getTaskID() << "].")
                            }
                        }
                    }
                }
                else
                {
                    CERR_FILE_LINE_MSG("ERROR::ProcessUniqueAutomationResponse: TaskId[" << taskId << "] not found.")
                }
            }
            if (itUniqueAutomationRequest->second->getOriginalRequest()->getOperatingRegion() > 0)
            {
                auto itOperatingRegion = m_idVsOperatingRegion.find(itUniqueAutomationRequest->second->getOriginalRequest()->getOperatingRegion());
                if (itOperatingRegion != m_idVsOperatingRegion.end())
                {
                    for (auto& keepInArea : itOperatingRegion->second->getKeepInAreas())
                    {
                        auto itKeepInArea = m_idVsZone.find(keepInArea);
                        if (itKeepInArea != m_idVsZone.end())
                        {
                            std::string fileName = savePath + "ZoneKeepIn_Id_" + std::to_string(keepInArea) + ".xml";
                            std::ofstream file(fileName);
                            file << itKeepInArea->second->toXML();
                            file.close();
                        }
                        else
                        {
                            CERR_FILE_LINE_MSG("ERROR::ProcessUniqueAutomationResponse: KeepIn area [" << keepInArea << "] not found for operating region [" << itOperatingRegion->second->getID() << "].")
                        }

                    }
                    for (auto& keepOutArea : itOperatingRegion->second->getKeepOutAreas())
                    {
                        auto itKeepOutArea = m_idVsZone.find(keepOutArea);
                        if (itKeepOutArea != m_idVsZone.end())
                        {
                            std::string fileName = savePath + "ZoneKeepOut_Id_" + std::to_string(keepOutArea) + ".xml";
                            std::ofstream file(fileName);
                            file << itKeepOutArea->second->toXML();
                            file.close();
                        }
                        else
                        {
                            CERR_FILE_LINE_MSG("ERROR::ProcessUniqueAutomationResponse: KeepOut area [" << keepOutArea << "] not found for operating region [" << itOperatingRegion->second->getID() << "].")
                        }

                    }
                }
                else
                {
                    CERR_FILE_LINE_MSG("ERROR::ProcessUniqueAutomationResponse: could not find operating region [" << itUniqueAutomationRequest->second->getOriginalRequest()->getOperatingRegion() << "].")
                }
            } //if (itUniqueAutomationRequest->second->getOriginalRequest()->getOperatingRegion() > 0)
            std::string fileName = savePath + "UniqueAutomationResponse_Id_" + std::to_string(uniqueAutomationResponse->getResponseID()) + ".xml";
            std::ofstream file(fileName);
            file << uniqueAutomationResponse->toXML();
            file.close();

            // 5) save python plot file
            SavePythonScripts(savePath);
        }
        else //if(isSucceeded)
        {

            CERR_FILE_LINE_MSG("ERROR::ProcessUniqueAutomationResponse: bCreateUniqueDirectory failed ERRORS[" << sstrErrors.str() << "].")
        } //if(isSucceeded)


    }

}

void AutomationDiagramDataService::SavePythonScripts(const std::string & savePath)
{

    std::string fileName = savePath + "PlotAutomationDiagram.py";
    std::ofstream file(fileName);
#include "PlotAutomationDiagram.code"
    file.close();

    fileName = savePath + "ProcessUniqueAutomationResponse.py";
    file.open(fileName);
#include "ProcessUniqueAutomationResponse.code"
    file.close();

    fileName = savePath + "ProcessTasks.py";
    file.open(fileName);
#include "ProcessTasks.code"
    file.close();

    fileName = savePath + "ProcessEntityStates.py";
    file.open(fileName);
#include "ProcessEntityStates.code"
    file.close();

    fileName = savePath + "ProcessZones.py";
    file.open(fileName);
#include "ProcessZones.code"
    file.close();

}

}; //namespace data
}; //namespace service
}; //namespace uxas

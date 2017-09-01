// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "MessageLoggerForTestService.h"

#include "UxAS_Log.h"
//#include "Constants/UxAS_String.h"
//#include "UxAS_XmlUtil.h"

#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/SessionStatus.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/cmasi/CameraConfiguration.h"
#include "afrl/cmasi/autonomymonitor/TaskStatusRequest.h"
#include "afrl/cmasi/autonomymonitor/TaskFailure.h"
#include "afrl/cmasi/autonomymonitor/TaskSuccess.h"
#include "afrl/cmasi/autonomymonitor/TaskMonitorStarted.h"


#include <chrono>
#include <thread>
#include <cstdint>

#define STRING_XML_TRAJECTORY_RECORD "TrajectoryRecord"
#define STRING_XML_SUBSCRIPTION_ADDRESS "Subscription"
#define STRING_XML_LMCP_NAME "LmcpName"
#define STRING_XML_FILTERING_FIELD_NAME "FilteringFieldName"
#define STRING_XML_FILTERING_FIELD_VALUE "FilteringFieldValue"
#define STRING_XML_FIELD_NAME "FieldName"
#define TASK_STATUS_WAIT_TIMEOUT_MS 20000

namespace uxas
{
namespace service
{
namespace test
{

MessageLoggerForTestService::ServiceBase::CreationRegistrar<MessageLoggerForTestService> 
        MessageLoggerForTestService::s_registrar(MessageLoggerForTestService::s_registryServiceTypeNames());

MessageLoggerForTestService::MessageLoggerForTestService()
: ServiceBase(MessageLoggerForTestService::s_typeName(), MessageLoggerForTestService::s_directoryName())
{
    staliroTrajectoryPopulator = new testgeneration::staliro::c_TrajectoryPopulator;
    lastReceivedSimTime = 0;
};

MessageLoggerForTestService::~MessageLoggerForTestService()
{
};

bool
MessageLoggerForTestService::configure(const pugi::xml_node& serviceXmlNode)
{
    staliroInterface = testgeneration::staliro::c_CommunicationInterface::getInstance();
    
    addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
    addSubscriptionAddress(afrl::cmasi::SessionStatus::Subscription);
    addSubscriptionAddress(afrl::cmasi::autonomymonitor::TaskSuccess::Subscription);
    addSubscriptionAddress(afrl::cmasi::autonomymonitor::TaskFailure::Subscription);
    addSubscriptionAddress(afrl::cmasi::autonomymonitor::TaskMonitorStarted::Subscription);
    int32_t position = 0;
    
    for (pugi::xml_node currentXmlNode = serviceXmlNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
    {
        if (std::string(STRING_XML_TRAJECTORY_RECORD) == currentXmlNode.name())
        {
            std::string subscriptionAddress = currentXmlNode.attribute(STRING_XML_SUBSCRIPTION_ADDRESS).value();
            if (!subscriptionAddress.empty())
            {
                addSubscriptionAddress(subscriptionAddress);
            }
            trajectoryMapping[position].push_back(currentXmlNode.attribute(STRING_XML_LMCP_NAME).value());
            trajectoryMapping[position].push_back(currentXmlNode.attribute(STRING_XML_FILTERING_FIELD_NAME).value());
            trajectoryMapping[position].push_back(currentXmlNode.attribute(STRING_XML_FILTERING_FIELD_VALUE).value());
            trajectoryMapping[position].push_back(currentXmlNode.attribute(STRING_XML_FIELD_NAME).value());
            position++;
        }
    }

    return (true);
};

bool
MessageLoggerForTestService::initialize()
{
    return (true);
};

bool
MessageLoggerForTestService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::processReceivedLmcpMessage BEFORE logging received message");
    
    if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::autonomymonitor::TaskMonitorStarted::TypeName)
    {
        taskStatusResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskFailure>(receivedLmcpMessage->m_object)->getTaskID()] = 0;
        taskRobustnessResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskFailure>(receivedLmcpMessage->m_object)->getTaskID()] = 1.0;
    }
    else if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::autonomymonitor::TaskFailure::TypeName)
    {
        taskStatusResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskFailure>(receivedLmcpMessage->m_object)->getTaskID()] = -1;
        taskRobustnessResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskFailure>(receivedLmcpMessage->m_object)->getTaskID()] 
                = std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskFailure>(receivedLmcpMessage->m_object)->getRobustness();
    }
    else if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::autonomymonitor::TaskSuccess::TypeName)
    {
        taskStatusResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskSuccess>(receivedLmcpMessage->m_object)->getTaskID()] = 1;
        taskRobustnessResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskSuccess>(receivedLmcpMessage->m_object)->getTaskID()] 
                = std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskSuccess>(receivedLmcpMessage->m_object)->getRobustness();
    }
    
    if (staliroInterface->getSimulationStatus() == 1)
    {
        if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::AirVehicleConfiguration::TypeName)
        {
            afrl::cmasi::AirVehicleConfiguration* airVehicleConfig = 
                    (afrl::cmasi::AirVehicleConfiguration*) receivedLmcpMessage->m_object.get();
            
            std::vector< afrl::cmasi::PayloadConfiguration* > payloadConfigList = 
                    airVehicleConfig->getPayloadConfigurationList();
            
            for (std::vector< afrl::cmasi::PayloadConfiguration* >::iterator plIter = payloadConfigList.begin(); 
                    plIter < payloadConfigList.end(); 
                    plIter++)
            {
                if ((*plIter)->getLmcpTypeName() == "CameraConfiguration")
                {
                    uint32_t horRes = static_cast<afrl::cmasi::CameraConfiguration*>(*plIter)->getVideoStreamHorizontalResolution();
                    uint32_t verRes = static_cast<afrl::cmasi::CameraConfiguration*>(*plIter)->getVideoStreamVerticalResolution();
                    staliroTrajectoryPopulator->setCameraPixelCount(airVehicleConfig->getID(), horRes, verRes);
                }
            }
        }
        else if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::SessionStatus::TypeName)
        {
            afrl::cmasi::SessionStatus* sessionStatus = static_cast<afrl::cmasi::SessionStatus*> (receivedLmcpMessage->m_object.get());
            lastReceivedSimTime = sessionStatus->getScenarioTime();
            if (sessionStatus->getScenarioTime() > staliroInterface->getMaxSimulationDuration())
            {
                staliroInterface->sendHeartBeat(sessionStatus->getScenarioTime());
                
                auto taskStatusRequestMsg = std::make_shared<afrl::cmasi::autonomymonitor::TaskStatusRequest>();
                taskStatusRequestMsg->setTaskID(-1); //-1 for all tasks!
                sendSharedLmcpObjectBroadcastMessage(taskStatusRequestMsg);
                sendOutTrajectory();
                staliroInterface->setSimulationStatus(2); //Stop collecting trajectory 
            }
            else
            {
                staliroInterface->sendHeartBeat(sessionStatus->getScenarioTime());
            }
        }
        staliroTrajectoryPopulator->populateTrajectory((void *) receivedLmcpMessage->m_object.get(), &trajectory, &trajectoryMapping);
    }
    else if (staliroInterface->getSimulationStatus() == 2)
    {
        bool allDone = true;
        for (auto it = taskStatusResults.begin(); it != taskStatusResults.end(); it++)
        {
            if (it->second == 0)
            {
                allDone = false;
                break;
            }
        }
        if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::SessionStatus::TypeName)
        {
            afrl::cmasi::SessionStatus* sessionStatus = static_cast<afrl::cmasi::SessionStatus*> (receivedLmcpMessage->m_object.get());
            int64_t timePassed = sessionStatus->getScenarioTime() - lastReceivedSimTime;
            if (timePassed / sessionStatus->getRealTimeMultiple() > TASK_STATUS_WAIT_TIMEOUT_MS)
            {
                allDone = true;
            }
        }
        if (allDone)
        {
            sendMonitorResults();
            staliroInterface->sendEndOfSimulation();
            staliroInterface->setSimulationStatus(3);
        }
        else
        {
            auto taskStatusRequestMsg = std::make_shared<afrl::cmasi::autonomymonitor::TaskStatusRequest>();
            taskStatusRequestMsg->setTaskID(-1); //-1 for all tasks!
            sendSharedLmcpObjectBroadcastMessage(taskStatusRequestMsg);
        }
    }

    return (false); // always false implies never terminating service from here
};

void
MessageLoggerForTestService::sendOutTrajectory()
{
    uint32_t totalNumOfRows = trajectory.size();
    uint32_t curRow = 0;
    
    for (auto const &trajIter : trajectory)
    {
        curRow++;
        staliroInterface->addTrajectoryRow(curRow, 
                totalNumOfRows, 
                trajIter.second.size(), 
                (double) ((double) trajIter.first)/1000.0,
                (double *) &trajIter.second[0],
                & staliroTrajectoryPopulator->vehicleTrajectoryStartIndex);
    }
}

void MessageLoggerForTestService::sendMonitorResults()
{
    for (auto iter = taskStatusResults.begin(); iter != taskStatusResults.end(); iter++)
    {
        staliroInterface->sendTaskStatus((int32_t) iter->first, iter->second, taskRobustnessResults[iter->first]);
    }
}

}; //namespace test
}; //namespace service
}; //namespace uxas

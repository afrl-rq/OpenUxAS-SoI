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


#include <chrono>
#include <thread>
#include <cstdint>

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
    // taskStatusResults[1000] = 0;
    // taskRobustnessResults[1000] = 1.0;
};

MessageLoggerForTestService::~MessageLoggerForTestService()
{
};

bool
MessageLoggerForTestService::configure(const pugi::xml_node& serviceXmlNode)
{
    staliroInterface = testgeneration::staliro::c_CommunicationInterface::getInstance();
    
    addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(afrl::cmasi::SessionStatus::Subscription);
    addSubscriptionAddress(afrl::cmasi::autonomymonitor::TaskSuccess::Subscription);
    addSubscriptionAddress(afrl::cmasi::autonomymonitor::TaskFailure::Subscription);

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
    
    if (staliroInterface->getSimulationStatus() == 1)
    {
        if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::AirVehicleState::TypeName)
        {
            staliroTrajectoryPopulator->populateTrajectory((void *) receivedLmcpMessage->m_object.get(), &trajectory);
        }
        else if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::AirVehicleConfiguration::TypeName)
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
                    
                    //staliroTrajectoryPopulator->setCameraPixelCount(airVehicleConfig->getID(), horRes, verRes);
                }
            }           
        }
        else if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::SessionStatus::TypeName)
        {
            afrl::cmasi::SessionStatus* sessionStatus = static_cast<afrl::cmasi::SessionStatus*> (receivedLmcpMessage->m_object.get());
            if (sessionStatus->getScenarioTime() > staliroInterface->getMaxSimulationDuration())
            {
                staliroInterface->sendHeartBeat(sessionStatus->getScenarioTime());
                
                auto taskStatusRequestMsg = std::make_shared<afrl::cmasi::autonomymonitor::TaskStatusRequest>();
                taskStatusRequestMsg->setTaskID(-1); //-1 for all tasks!
                sendSharedLmcpObjectBroadcastMessage(taskStatusRequestMsg);
                staliroInterface->setSimulationStatus(2); //Stop collecting trajectory 
                std::cout << "Simulation status :2" << std::endl;
            }
            else
            {
                staliroInterface->sendHeartBeat(sessionStatus->getScenarioTime());
            }
        }
    }
    else 
    {
        if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::autonomymonitor::TaskFailure::TypeName)
        {
            std::cout << "Task Failure" << std::endl;
            std::cout << std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskFailure>(receivedLmcpMessage->m_object)->getTaskID() << std::endl;
            taskStatusResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskFailure>(receivedLmcpMessage->m_object)->getTaskID()] = -1;
            taskRobustnessResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskFailure>(receivedLmcpMessage->m_object)->getTaskID()] = 1.0;
            // fill in a data structure for task monitoring
        }
        else if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::autonomymonitor::TaskSuccess::TypeName)
        {
            std::cout << "TaskSuccess" << std::endl;
            std::cout << std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskSuccess>(receivedLmcpMessage->m_object)->getTaskID() << std::endl;
            taskStatusResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskSuccess>(receivedLmcpMessage->m_object)->getTaskID()] = 1;
            taskRobustnessResults[std::static_pointer_cast<afrl::cmasi::autonomymonitor::TaskSuccess>(receivedLmcpMessage->m_object)->getTaskID()] = 1.0;
            // fill in a data structure for task monitoring
        }
        if (staliroInterface->getSimulationStatus() == 2)
        {
            std::cout << "send trajectory" << std::endl;
            sendOutTrajectory();
            staliroInterface->setSimulationStatus(3); // Will read monitoring results
            std::cout << "Sim status 3" << std::endl;
        }
        else if (staliroInterface->getSimulationStatus() == 3)
        {
            std::cout << "checking all done" << std::endl;
            bool allDone = true;
            for (auto it = taskStatusResults.begin(); it != taskStatusResults.end(); it++)
            {
                if (it->second == 0)
                {
                    allDone = false;
                    break;
                }
            }
            if (allDone)
            {
                staliroInterface->setSimulationStatus(4);
                std::cout << "sim status 4" << std::endl;
            }
        }
        else if (staliroInterface->getSimulationStatus() == 4) // Will send monitoring results
        {
            std::cout << "sendMonitorResults" << std::endl;
            sendMonitorResults();
            std::cout << "sendEndOfSimulation" << std::endl;
            staliroInterface->sendEndOfSimulation();
            std::cout << "DONE" << std::endl;
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
                (double *) &trajIter.second[0]);
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

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
    staliroTrajectoryPopulator = new testgeneration::staliro::c_TrajectoryPopulator();
};

MessageLoggerForTestService::~MessageLoggerForTestService()
{
};

bool
MessageLoggerForTestService::configure(const pugi::xml_node& serviceXmlNode)
{
    staliroInterface = testgeneration::staliro::c_CommunicationInterface::getInstance();
    
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(afrl::cmasi::SessionStatus::Subscription);

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
    
    if (staliroInterface->isTrajectoryRequested())
    {
        if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::AirVehicleState::TypeName)
        {
            staliroTrajectoryPopulator->populateTrajectory((void *) receivedLmcpMessage->m_object.get(), &trajectory);
        }
        else if (receivedLmcpMessage->m_object->getLmcpTypeName() == afrl::cmasi::SessionStatus::TypeName)
        {
            afrl::cmasi::SessionStatus* sessionStatus = static_cast<afrl::cmasi::SessionStatus*> (receivedLmcpMessage->m_object.get());
            if (sessionStatus->getScenarioTime() > staliroInterface->getMaxSimulationDuration())
            {
                sendOutTrajectory();
            }
            else
            {
                staliroInterface->sendHeartBeat(sessionStatus->getScenarioTime());
            }
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

}; //namespace test
}; //namespace service
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_SerialAutomationRequest.cpp
 * Author: derek
 * 
 * Created on Aug 24, 2015, 9:31 AM
 */

#include "SerialAutomationRequestTestService.h"

#include "UxAS_Log.h"
#include "UxAS_TimerManager.h"
#include "pugixml.hpp"
#include "TimeUtilities.h"

#define STRING_COMPONENT_NAME "SerialAutomationRequest"
#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME
#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_MAX_RESPONSE_TIME_MS "MaxResponseTime_ms"

namespace uxas
{
namespace service
{
namespace test
{
SerialAutomationRequestTestService::ServiceBase::CreationRegistrar<SerialAutomationRequestTestService>
SerialAutomationRequestTestService::s_registrar(SerialAutomationRequestTestService::s_registryServiceTypeNames());

SerialAutomationRequestTestService::SerialAutomationRequestTestService()
: ServiceBase(SerialAutomationRequestTestService::s_typeName(), SerialAutomationRequestTestService::s_directoryName())
{
};

SerialAutomationRequestTestService::~SerialAutomationRequestTestService()
{
    uint64_t delayTime_ms{1000};
    if (m_responseTimerId && !uxas::common::TimerManager::getInstance().destroyTimer(m_responseTimerId, delayTime_ms))
    {
        LOG_WARN("SerialAutomationRequestTestService::~SerialAutomationRequestTestService failed to destroy response timer "
                "(m_responseTimerId) with timer ID ", m_responseTimerId, " within ", delayTime_ms, " millisecond timeout");
    }
};

bool
SerialAutomationRequestTestService::configure(const pugi::xml_node& ndComponent)

{
    bool isSucceeded(true);
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();
    //assert(strComponentType==STRING_XML_COMPONENT_TYPE)

    if (!ndComponent.attribute(STRING_XML_MAX_RESPONSE_TIME_MS).empty())
    {
        m_maxResponseTime_ms = ndComponent.attribute(STRING_XML_MAX_RESPONSE_TIME_MS).as_uint();
    }

    addSubscriptionAddress(afrl::cmasi::AutomationRequest::Subscription);
    addSubscriptionAddress(afrl::impact::ImpactAutomationRequest::Subscription);
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    addSubscriptionAddress(afrl::impact::ImpactAutomationResponse::Subscription);

    return (isSucceeded);
}

bool
SerialAutomationRequestTestService::initialize()
{
    // create timer
    m_responseTimerId = uxas::common::TimerManager::getInstance().createTimer(
            std::bind(&SerialAutomationRequestTestService::OnResponseTimeout, this), "SerialAutomationRequestTestService::OnResponseTimeout");

    return true;
}

bool
SerialAutomationRequestTestService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
        if (afrl::cmasi::isAutomationRequest(receivedLmcpMessage->m_object.get()) || afrl::impact::isImpactAutomationRequest(receivedLmcpMessage->m_object.get()))
        {
            if (m_waitingRequests.empty() && m_isAllClear)
            {
                m_isAllClear = false;
                sendSharedLmcpObjectLimitedCastMessage("UniqueAutomationRequest", receivedLmcpMessage->m_object);

                // reset the timer
                uxas::common::TimerManager::getInstance().startSingleShotTimer(m_responseTimerId, m_maxResponseTime_ms);
            }
            else
            {
                m_waitingRequests.push_back(receivedLmcpMessage->m_object);
            }
        }
        else if (afrl::cmasi::isAutomationResponse(receivedLmcpMessage->m_object.get()) || afrl::impact::isImpactAutomationResponse(receivedLmcpMessage->m_object.get()))
        {
            OnResponseTimeout();
        }
        return false;
}

void SerialAutomationRequestTestService::OnResponseTimeout()
{
    if (m_waitingRequests.empty())
    {
        m_isAllClear = true;
    }
    else
    {
        std::shared_ptr<avtas::lmcp::Object> toSend = m_waitingRequests.front();
        m_waitingRequests.pop_front();
        sendSharedLmcpObjectLimitedCastMessage("UniqueAutomationRequest", toSend);

        // reset the timer
        uxas::common::TimerManager::getInstance().startSingleShotTimer(m_responseTimerId, m_maxResponseTime_ms);
    }
}

}; //namespace test
}; //namespace service
}; //namespace uxas

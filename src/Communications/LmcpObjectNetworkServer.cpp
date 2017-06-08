// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectNetworkServer.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"

namespace uxas
{
namespace communications
{

LmcpObjectNetworkServer::LmcpObjectNetworkServer()
{
};

LmcpObjectNetworkServer::~LmcpObjectNetworkServer()
{
    if (m_thread && m_thread->joinable())
    {
        m_thread->detach();
    }
};

bool
LmcpObjectNetworkServer::configure()
{
    m_entityId = uxas::common::ConfigurationManager::getInstance().getEntityId();
    return (true);
};

bool
LmcpObjectNetworkServer::initializeAndStart()
{
    bool isStarted{false};
    isStarted = initialize();

    if (isStarted)
    {
        m_thread = uxas::stduxas::make_unique<std::thread>(&LmcpObjectNetworkServer::executeNetworkServer, this);
        UXAS_LOG_INFORM("LmcpObjectNetworkServer::initializeAndStart started LMCP network server processing thread [", m_thread->get_id(), "]");
    }
    return (isStarted);
}

void
LmcpObjectNetworkServer::terminate()
{
    m_isTerminate = true;
}

bool
LmcpObjectNetworkServer::initialize()
{
    m_lmcpObjectMessageReceiverPipe.initializePull(m_entityId, m_networkId);
    m_lmcpObjectMessageSenderPipe.initializePublish("", m_entityId, m_networkId);
    UXAS_LOG_INFORM("LmcpObjectNetworkServer initialized LMCP network pull receiver and publish sender pipes");

    return (true);
};

void
LmcpObjectNetworkServer::executeNetworkServer()
{
    while (!m_isTerminate)
    {
        // get the next LMCP object message (if any) sent to the LMCP network hub
        std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> receivedLmcpMessage 
                = m_lmcpObjectMessageReceiverPipe.getNextSerializedMessage();
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("LmcpObjectNetworkServer::executeNetworkServer RECEIVED serialized message");
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("Address:          [", receivedLmcpMessage->getAddress(), "]");
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("ContentType:      [", receivedLmcpMessage->getMessageAttributesReference()->getContentType(), "]");
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("Descriptor:       [", receivedLmcpMessage->getMessageAttributesReference()->getDescriptor(), "]");
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("SourceGroup:      [", receivedLmcpMessage->getMessageAttributesReference()->getSourceGroup(), "]");
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("SourceEntityId:   [", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId(), "]");
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("SourceServiceId:  [", receivedLmcpMessage->getMessageAttributesReference()->getSourceServiceId(), "]");
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("AttributesString: [", receivedLmcpMessage->getMessageAttributesReference()->getString(), "]");
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("getPayload:       [", receivedLmcpMessage->getPayload(), "]");
        UXAS_LOG_DEBUG_VERBOSE_MESSAGING("getString:        [", receivedLmcpMessage->getString(), "]");

        if (receivedLmcpMessage)
        {
            m_lmcpObjectMessageSenderPipe.sendSerializedMessage(std::move(receivedLmcpMessage));
            UXAS_LOG_DEBUG_VERBOSE_MESSAGING("LmcpObjectNetworkServer::executeNetworkServer SENT serialized message");
        }
    }
    UXAS_LOG_INFORM("LmcpObjectNetworkServer::executeSerializedNetworkClient exiting infinite loop thread [", std::this_thread::get_id(), "]");
};

}; //namespace communications
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectNetworkPublishPullBridge.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"

#include "avtas/lmcp/Factory.h"

#include <sstream>
#include <iostream>

#define STRING_XML_ADDRESS_PULL "AddressPULL"
#define STRING_XML_ADDRESS_PUB "AddressPUB"

namespace uxas {
namespace communications {

LmcpObjectNetworkPublishPullBridge::LmcpObjectNetworkPublishPullBridge()
{
};

LmcpObjectNetworkPublishPullBridge::~LmcpObjectNetworkPublishPullBridge()
{
    if (m_externalReceiveProcessingThread && m_externalReceiveProcessingThread->joinable())
    {
        m_externalReceiveProcessingThread->detach();
    }
};

bool
LmcpObjectNetworkPublishPullBridge::configure(const pugi::xml_node& bridgeXmlNode)
{
    bool isSuccess{true};

    if (!bridgeXmlNode.attribute(STRING_XML_ADDRESS_PULL).empty())
    {
        m_externalPullSocketAddress = bridgeXmlNode.attribute(STRING_XML_ADDRESS_PULL).value();
        UXAS_LOG_INFORM(s_typeName(), "::configure setting external pull socket address to ", m_externalPullSocketAddress, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure failed to find external pull socket address in XML configuration; external pull socket address is ", m_externalPullSocketAddress);
    }

    if (!bridgeXmlNode.attribute(STRING_XML_ADDRESS_PUB).empty())
    {
        m_externalPublishSocketAddress = bridgeXmlNode.attribute(STRING_XML_ADDRESS_PUB).value();
        UXAS_LOG_INFORM(s_typeName(), "::configure setting external pub socket address to ", m_externalPublishSocketAddress, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure failed to find external pub socket in XML configuration; external pub socket is ", m_externalPublishSocketAddress);
    }
    
    if (!bridgeXmlNode.attribute("ConsiderSelfGenerated").empty())
    {
        m_isConsideredSelfGenerated = bridgeXmlNode.attribute("ConsiderSelfGenerated").as_bool();
        UXAS_LOG_INFORM(s_typeName(), "::configure setting 'ConsiderSelfGenerated' boolean to ", m_isConsideredSelfGenerated, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure did not find 'ConsiderSelfGenerated' boolean in XML configuration; 'ConsiderSelfGenerated' boolean is ", m_isConsideredSelfGenerated);
    }

    for (pugi::xml_node currentXmlNode = bridgeXmlNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
    {
        if (uxas::common::StringConstant::SubscribeToMessage() == currentXmlNode.name())
        {
            if (!currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).empty())
            {
                addSubscriptionAddress(currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).value());
            }
        }
    }

    // do not forward any uni-cast messages addressed to this bridge
    UXAS_LOG_INFORM(s_typeName(), "::configure adding non-forward address [", getNetworkClientUnicastAddress(m_entityId, m_networkId), "]");
    m_nonImportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));
    m_nonExportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));

    return (isSuccess);
};

bool
LmcpObjectNetworkPublishPullBridge::initialize()
{
    m_externalLmcpObjectMessageReceiverPipe.initializeExternalPull(m_entityId, m_networkId,
        m_externalPullSocketAddress, true);
    UXAS_LOG_INFORM(s_typeName(), " external pull socket address is ", m_externalPullSocketAddress);

    m_externalLmcpObjectMessageSenderPipe.initializeExternalPub(m_messageSourceGroup, m_entityId, m_networkId,
        m_externalPublishSocketAddress, true);
    UXAS_LOG_INFORM(s_typeName(), " external pub socket address is ", m_externalPublishSocketAddress);
    UXAS_LOG_INFORM(s_typeName(), "::initialize succeeded");
    return (true);
};

bool
LmcpObjectNetworkPublishPullBridge::start()
{
    m_externalReceiveProcessingThread = uxas::stduxas::make_unique<std::thread>(&LmcpObjectNetworkPublishPullBridge
        ::executeExternalSerializedLmcpObjectReceiveProcessing, this);
    UXAS_LOG_INFORM(s_typeName(), "::start pull receive processing thread [", m_externalReceiveProcessingThread->get_id(), "]");
    return (true);
};

bool
LmcpObjectNetworkPublishPullBridge::terminate()
{
    m_isTerminate = true;
    if (m_externalReceiveProcessingThread && m_externalReceiveProcessingThread->joinable())
    {
        m_externalReceiveProcessingThread->join();
        UXAS_LOG_INFORM(s_typeName(), "::terminate calling thread completed m_externalReceiveProcessingThread join");
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::terminate unexpectedly could not join m_externalReceiveProcessingThread");
    }
    return (true);
};

bool
LmcpObjectNetworkPublishPullBridge::processReceivedSerializedLmcpMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
    receivedLmcpMessage)
{
    // send message to the external entity
    UXAS_LOG_DEBUGGING(s_typeName(), "::processReceivedSerializedLmcpMessage before sending serialized message ",
        "having address ", receivedLmcpMessage->getAddress(),
        " and size ", receivedLmcpMessage->getPayload().size());

    // process messages from a local service (only)
    if (m_entityIdString == receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId())
    {
        if (m_nonExportForwardAddresses.find(receivedLmcpMessage->getAddress()) == m_nonExportForwardAddresses.end())
        {
            UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage processing message with source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId());
            m_externalLmcpObjectMessageSenderPipe.sendSerializedMessage(std::move(receivedLmcpMessage));
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage ignoring non-export message with address ", receivedLmcpMessage->getAddress(), ", source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceServiceId());
        }
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage ignoring message with source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId());
    }

    return (false); // always false implies never terminating bridge from here
};

void
LmcpObjectNetworkPublishPullBridge::executeExternalSerializedLmcpObjectReceiveProcessing()
{
    try
    {
        while (!m_isTerminate)
        {
            // TODO review IMPACT messaging requirements (need to modify object before sending?)
            std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> recvdAddAttMsg
                = m_externalLmcpObjectMessageReceiverPipe.getNextSerializedMessage();

            if (!recvdAddAttMsg)
            {
                // no message available
                continue;
            }

            // send message from the external entity to the local system
            UXAS_LOG_DEBUGGING(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing before sending serialized message ",
                "having address ", recvdAddAttMsg->getAddress(),
                " and size ", recvdAddAttMsg->getPayload().size());
            if (recvdAddAttMsg->isValid())
            {
                if (m_nonImportForwardAddresses.find(recvdAddAttMsg->getAddress()) == m_nonImportForwardAddresses.end())
                {
                    if(m_isConsideredSelfGenerated)
                    {
                        recvdAddAttMsg->updateSourceAttributes("PublishPullBridge", std::to_string(m_entityId), std::to_string(m_networkId));
                    }
                    sendSerializedLmcpObjectMessage(std::move(recvdAddAttMsg));
                }
                else
                {
                    UXAS_LOG_INFORM(s_typeName(), "::executeSerialReceiveProcessing ignoring non-import message with address ", recvdAddAttMsg->getAddress(), ", source entity ID ", recvdAddAttMsg->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", recvdAddAttMsg->getMessageAttributesReference()->getSourceServiceId());
                }
            }
            else
            {
                UXAS_LOG_WARN(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing ignoring received, invalid AddressedAttributedMessage object");
            }
        }
        UXAS_LOG_INFORM(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing exiting infinite loop thread [", std::this_thread::get_id(), "]");
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing EXCEPTION: ", ex.what());
    }
};

}; //namespace communications
}; //namespace uxas

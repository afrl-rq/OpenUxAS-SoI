// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectNetworkSubscribePushBridge.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"

#include "avtas/lmcp/Factory.h"

#include <sstream>
#include <iostream>

#define STRING_XML_SUBSCRIBE_TO_EXTERNAL_MESSAGE "SubscribeToExternalMessage"

#define STRING_XML_ADDRESS_SUB "AddressSUB"
#define STRING_XML_ADDRESS_PUSH "AddressPUSH"

namespace uxas {
namespace communications {

LmcpObjectNetworkSubscribePushBridge::LmcpObjectNetworkSubscribePushBridge()
{
};

LmcpObjectNetworkSubscribePushBridge::~LmcpObjectNetworkSubscribePushBridge()
{
    if (m_externalReceiveProcessingThread && m_externalReceiveProcessingThread->joinable())
    {
        m_externalReceiveProcessingThread->detach();
    }
};

bool
LmcpObjectNetworkSubscribePushBridge::configure(const pugi::xml_node& bridgeXmlNode)
{
    bool isSuccess{true};

    if (!bridgeXmlNode.attribute(STRING_XML_ADDRESS_SUB).empty())
    {
        m_externalSubscribeSocketAddress = bridgeXmlNode.attribute(STRING_XML_ADDRESS_SUB).value();
        UXAS_LOG_INFORM(s_typeName(), "::configure setting external subscribe socket address to ", m_externalSubscribeSocketAddress, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure failed to find external subscribe socket address in XML configuration; external subscribe socket address is ", m_externalSubscribeSocketAddress);
    }

    if (!bridgeXmlNode.attribute(STRING_XML_ADDRESS_PUSH).empty())
    {
        m_externalPushSocketAddress = bridgeXmlNode.attribute(STRING_XML_ADDRESS_PUSH).value();
        UXAS_LOG_INFORM(s_typeName(), "::configure setting external push socket address to ", m_externalPushSocketAddress, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure failed to find external push socket in XML configuration; external push socket is ", m_externalPushSocketAddress);
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
        else if (uxas::common::StringConstant::SubscribeToExternalMessage() == currentXmlNode.name())
        {
            if (!currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).empty())
            {
                m_externalSubscriptionAddresses.emplace(currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).value());
            }
        }
    }

    //
    // DESIGN 20150911 RJT message addressing - entity ID
    // - received/sent LMCP messages always include entity ID
    // - the entity cast address is derived from entity ID (see getEntityCastAddress function)
    // - bridges never subscribe to the entity cast address on the internal network
    // - bridges usually subscribe (or coordinate subscription) to the entity cast address on external networks
    //   (TCP and serial bridges do not have external subscription)
    //
    // subscribe to external messages addressed to this entity
    UXAS_LOG_INFORM(s_typeName(), "::configure externally subscribing to entity cast address [", getEntityCastAddress(m_entityId), "]");
    m_externalSubscriptionAddresses.emplace(getEntityCastAddress(m_entityId));

    // do not forward any uni-cast messages addressed to this bridge
    UXAS_LOG_INFORM(s_typeName(), "::configure adding non-forward address [", getNetworkClientUnicastAddress(m_entityId, m_networkId), "]");
    m_nonImportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));
    m_nonExportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));

    return (isSuccess);
};

bool
LmcpObjectNetworkSubscribePushBridge::initialize()
{
    m_externalLmcpObjectMessageReceiverPipe.initializeExternalSubscription(m_entityId, m_networkId,
        m_externalSubscribeSocketAddress, false);
    UXAS_LOG_INFORM(s_typeName(), " external subscribe socket address is ", m_externalSubscribeSocketAddress);

    if (m_externalSubscriptionAddresses.size() > 0)
    {
        for (const auto& lmcpExternalSubAddress : m_externalSubscriptionAddresses)
        {
            addSubscriptionAddress(lmcpExternalSubAddress);
            UXAS_LOG_INFORM(s_typeName(), " subscribing to external LMCP address [", lmcpExternalSubAddress, "]");
        }
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), " subscribing to zero LMCP addresses");
    }

    m_externalLmcpObjectMessageSenderPipe.initializeExternalPush(m_messageSourceGroup, m_entityId, m_networkId,
        m_externalPushSocketAddress, false);
    UXAS_LOG_INFORM(s_typeName(), " external push socket address is ", m_externalPushSocketAddress);
    UXAS_LOG_INFORM(s_typeName(), "::initialize succeeded");
    return (true);
};

bool
LmcpObjectNetworkSubscribePushBridge::start()
{
    m_externalReceiveProcessingThread = uxas::stduxas::make_unique<std::thread>(&LmcpObjectNetworkSubscribePushBridge
        ::executeExternalSerializedLmcpObjectReceiveProcessing, this);
    UXAS_LOG_INFORM(s_typeName(), "::start subscribe receive processing thread [", m_externalReceiveProcessingThread->get_id(), "]");
    return (true);
};

bool
LmcpObjectNetworkSubscribePushBridge::terminate()
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
LmcpObjectNetworkSubscribePushBridge::processReceivedSerializedLmcpMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
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
LmcpObjectNetworkSubscribePushBridge::executeExternalSerializedLmcpObjectReceiveProcessing()
{
    try
    {
        while (!m_isTerminate)
        {
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
                        recvdAddAttMsg->updateSourceAttributes("SubscribePushBridge", std::to_string(m_entityId), std::to_string(m_networkId));
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

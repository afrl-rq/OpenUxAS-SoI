// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================


#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"

#include "avtas/lmcp/Factory.h"

#include <sstream>
#include <iostream>
#include <locale>
#include "ZeroMqFabric.h"
#include "ImpactSubscribePushBridge.h"

#define STRING_XML_SUBSCRIBE_TO_EXTERNAL_MESSAGE "SubscribeToExternalMessage"

#define STRING_XML_ADDRESS_SUB "AddressSUB"
#define STRING_XML_ADDRESS_PUSH "AddressPUSH"
#define STRING_XML_EXTERNAL_ENTITY_ID "ExternalID"
#define STRING_XML_THROTTLE_CONFIGURATION_FORWARDING "ThrottleConfigurationForwarding"

namespace uxas {
namespace communications {

ImpactSubscribePushBridge::ImpactSubscribePushBridge()
{
};

ImpactSubscribePushBridge::~ImpactSubscribePushBridge()
{
    if (m_externalReceiveProcessingThread && m_externalReceiveProcessingThread->joinable())
    {
        m_externalReceiveProcessingThread->detach();
    }
};

bool
ImpactSubscribePushBridge::configure(const pugi::xml_node& bridgeXmlNode)
{
    // initialize external ID to be as if messages are generated locally
    m_externalID = m_entityId;

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

    if (!bridgeXmlNode.attribute(STRING_XML_EXTERNAL_ENTITY_ID).empty())
    {
        // set external ID from configuration, falling back to local ID if parse fails
        m_externalID = bridgeXmlNode.attribute(STRING_XML_EXTERNAL_ENTITY_ID).as_int64(m_entityId);
        UXAS_LOG_INFORM(s_typeName(), "::configure setting external ID to ", m_externalID, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure failed to external ID in XML configuration; external matches local ID as ", m_externalID);
    }

    if (!bridgeXmlNode.attribute(STRING_XML_THROTTLE_CONFIGURATION_FORWARDING).empty())
    {
        m_throttleConfigurationForwarding = bridgeXmlNode.attribute(STRING_XML_THROTTLE_CONFIGURATION_FORWARDING).as_bool();
        UXAS_LOG_INFORM(s_typeName(), "::configure setting 'throttle configuration forwarding' boolean to ", m_throttleConfigurationForwarding, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure failed to find 'throttle configuration forwarding' boolean in XML configuration; server boolean is ", m_throttleConfigurationForwarding);
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

    // handle all subscriptions, reminder: external subscriptions follow IMPACT subscription format
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

    // do not forward any uni-cast messages addressed to this bridge
    UXAS_LOG_INFORM(s_typeName(), "::configure adding non-forward address [", getNetworkClientUnicastAddress(m_entityId, m_networkId), "]");
    m_nonImportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));
    m_nonExportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));

    // self generated overrides configured reported entity ID
    if(m_isConsideredSelfGenerated)
    {
        m_externalID = m_entityId;
    }
    
    return (true); // no failure criteria for this configuration set, reverts to defaults
};

bool
ImpactSubscribePushBridge::initialize()
{
    int32_t zmqhighWaterMark{ 100000 };

    // push socket
    auto pushConfig = transport::ZeroMqSocketConfiguration(uxas::communications::transport::NETWORK_NAME::zmqLmcpNetwork(),
        m_externalPushSocketAddress, ZMQ_PUSH, false, false, zmqhighWaterMark, zmqhighWaterMark);

    try
    {
        sender = transport::ZeroMqFabric::getInstance().createSocket(pushConfig);
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR("ImpactSubscribePushBridge::initialize, create push socket EXCEPTION: ", ex.what());
        sender = nullptr;
        return false;
    }

    // sub socket
    auto subConfig = transport::ZeroMqSocketConfiguration(uxas::communications::transport::NETWORK_NAME::zmqLmcpNetwork(),
        m_externalSubscribeSocketAddress, ZMQ_SUB, false, true, zmqhighWaterMark, zmqhighWaterMark);
    try
    {
        subscriber = transport::ZeroMqFabric::getInstance().createSocket(subConfig);
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR("ImpactSubscribePushBridge::initialize, create subscribe socket EXCEPTION: ", ex.what());
        subscriber = nullptr;
        return false;
    }
    
    // loop through m_externalSubscriptionAddresses and subscribe following IMPACT message addressing
    for (auto externalSubscription : m_externalSubscriptionAddresses)
    {
        subscriber->setsockopt(ZMQ_SUBSCRIBE, externalSubscription.c_str(), externalSubscription.size());
    }

    UXAS_LOG_INFORM(s_typeName(), "::initialize succeeded");
    return (true);
};

bool
ImpactSubscribePushBridge::start()
{
    m_externalReceiveProcessingThread = uxas::stduxas::make_unique<std::thread>(&ImpactSubscribePushBridge
        ::executeExternalSerializedLmcpObjectReceiveProcessing, this);
    UXAS_LOG_INFORM(s_typeName(), "::start subscribe receive processing thread [", m_externalReceiveProcessingThread->get_id(), "]");
    return (true);
};

bool
ImpactSubscribePushBridge::terminate()
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
ImpactSubscribePushBridge::processReceivedSerializedLmcpMessage(
    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> receivedLmcpMessage)
{
    // send message to the external entity
    UXAS_LOG_DEBUGGING(s_typeName(), "::processReceivedSerializedLmcpMessage before sending serialized message ",
        "having address ", receivedLmcpMessage->getAddress(),
        " and size ", receivedLmcpMessage->getPayload().size());

    // process messages from a local service (only)
    if (m_entityIdString != receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId())
      return false;

    // do not forward uni-cast messages (or any address on blocked list)
    if (m_nonExportForwardAddresses.find(receivedLmcpMessage->getAddress()) == m_nonExportForwardAddresses.end())
    {
        UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage processing message with source service ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceServiceId());

        // unpack message to get complete attributes
        std::string message = receivedLmcpMessage->getPayload();
        avtas::lmcp::ByteBuffer byteBuffer;
        byteBuffer.allocate(message.size());
        byteBuffer.put(reinterpret_cast<const uint8_t*> (message.c_str()), message.size());
        byteBuffer.rewind();

        std::shared_ptr<avtas::lmcp::Object> ptr_Object;
        ptr_Object.reset(avtas::lmcp::Factory::getObject(byteBuffer));
        if(!ptr_Object)
        {
            UXAS_LOG_WARN(s_typeName(), "::processReceivedSerializedLmcpMessage received an invalid LMCP object, ignoring");
            return false;
        }

        // check for air vehicle configuration throttling
        if (m_throttleConfigurationForwarding && std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(ptr_Object))
        {
            auto config = std::static_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(ptr_Object);
            if (m_configs.find(config->getID()) != m_configs.end())
            {
                if (m_configs[config->getID()]->toXML().compare(config->toXML()) == 0)
                {
                    UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage blocking AirVehicleConfiguration, already sent" );
                    return false; // don't forward configs already forwarded
                }
            }
            m_configs[config->getID()] = config;
        }

        // build IMPACT messaging address 'lmcp:[MDM SERIES NAME]:[message type name]'
        std::string seriesName = ptr_Object->getSeriesName();

        // convert seriesName to uppercase
        std::transform(seriesName.begin(), seriesName.end(), seriesName.begin(), toupper);

        std::string impact_address = "lmcp:" + seriesName + ":" + ptr_Object->getLmcpTypeName();
        n_ZMQ::s_sendmore(*sender, impact_address);
        n_ZMQ::s_send(*sender, receivedLmcpMessage->getPayload());
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage ignoring non-export message with address ", receivedLmcpMessage->getAddress(), ", source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceServiceId());
    }

    return (false); // always false implies never terminating bridge from here
}

void
ImpactSubscribePushBridge::executeExternalSerializedLmcpObjectReceiveProcessing()
{
    try
    {
        while (!m_isTerminate)
        {
            std::string impact_address = n_ZMQ::s_recv(*subscriber);
            std::string message = n_ZMQ::s_recv(*subscriber);

            // ignore impact address, construct UxAS address from valid LMCP message
            avtas::lmcp::ByteBuffer byteBuffer;
            byteBuffer.allocate(message.size());
            byteBuffer.put(reinterpret_cast<const uint8_t*> (message.c_str()), message.size());
            byteBuffer.rewind();

            std::shared_ptr<avtas::lmcp::Object> ptr_Object;
            ptr_Object.reset(avtas::lmcp::Factory::getObject(byteBuffer));
            
            if(ptr_Object)
            {
                auto broadcast_address = ptr_Object->getFullLmcpTypeName();
                std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> recvdAddAttMsg = uxas::stduxas::make_unique<uxas::communications::data::AddressedAttributedMessage>();

                // internal message addressing is formatted as 'broadcast' from 'fusion' group
                // with entity ID set from configuration
                recvdAddAttMsg->setAddressAttributesAndPayload(broadcast_address, "lmcp", broadcast_address, "fusion", std::to_string(m_externalID), std::to_string(m_networkId), message);

                // send message from the external entity to the local bus
                if (recvdAddAttMsg->isValid())
                {
                    UXAS_LOG_DEBUGGING(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing before sending serialized message ",
                        "having address ", recvdAddAttMsg->getAddress(),
                        " and size ", recvdAddAttMsg->getPayload().size());

                    sendSerializedLmcpObjectMessage(std::move(recvdAddAttMsg));
                }
                else
                {
                    UXAS_LOG_WARN(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing ignoring received, invalid AddressedAttributedMessage object");
                }
            }
            else
            {
                UXAS_LOG_WARN(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing ignoring invalid LMCP object");
            }
        }
        UXAS_LOG_INFORM(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing exiting infinite loop thread [", std::this_thread::get_id(), "]");
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing EXCEPTION: ", ex.what());
    }
}

}; //namespace communications
}; //namespace uxas

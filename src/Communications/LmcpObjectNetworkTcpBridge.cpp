// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectNetworkTcpBridge.h"

#include "avtas/lmcp/Factory.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"
#include "UxAS_Time.h"

#include "stdUniquePtr.h"

#include <chrono>
#include <sstream>
#include <iostream>
#include <iomanip>
#include <thread>

//#define IMPACT_BUILD

// IMPACT AMASE THROTTLE
#ifdef IMPACT_BUILD
#include <unordered_set>
#include "afrl/impact/IMPACT.h"
#include "afrl/cmasi/CMASI.h"
#endif

namespace uxas
{
namespace communications
{

LmcpObjectNetworkTcpBridge::LmcpObjectNetworkTcpBridge()
{
};

LmcpObjectNetworkTcpBridge::~LmcpObjectNetworkTcpBridge()
{
    if (m_tcpProcessingThread && m_tcpProcessingThread->joinable())
    {
        m_tcpProcessingThread->detach();
    }
};

bool
LmcpObjectNetworkTcpBridge::configure(const pugi::xml_node& bridgeXmlNode)
{
    bool isSuccess{true};

    if (!bridgeXmlNode.attribute(uxas::common::StringConstant::TcpAddress().c_str()).empty())
    {
        m_tcpReceiveSendAddress = bridgeXmlNode.attribute(uxas::common::StringConstant::TcpAddress().c_str()).value();
        UXAS_LOG_INFORM(s_typeName(), "::configure setting TCP address to ", m_tcpReceiveSendAddress, " from XML configuration");
    }
    else
    {
        isSuccess = false;
        UXAS_LOG_ERROR(s_typeName(), "::configure failed to find TCP address in XML configuration");
    }

    if (isSuccess)
    {
        if (!bridgeXmlNode.attribute(uxas::common::StringConstant::Server().c_str()).empty())
        {
            m_isServer = bridgeXmlNode.attribute(uxas::common::StringConstant::Server().c_str()).as_bool();
            UXAS_LOG_INFORM(s_typeName(), "::configure setting server boolean to ", m_isServer, " from XML configuration");
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::configure did not find server boolean in XML configuration; server boolean is ", m_isServer);
        }
    }

    if (isSuccess)
    {
        if (!bridgeXmlNode.attribute("ConsiderSelfGenerated").empty())
        {
            m_isConsideredSelfGenerated = bridgeXmlNode.attribute("ConsiderSelfGenerated").as_bool();
            UXAS_LOG_INFORM(s_typeName(), "::configure setting 'ConsiderSelfGenerated' boolean to ", m_isConsideredSelfGenerated, " from XML configuration");
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::configure did not find 'ConsiderSelfGenerated' boolean in XML configuration; 'ConsiderSelfGenerated' boolean is ", m_isConsideredSelfGenerated);
        }
    }
    
    if (isSuccess)
    {
        for (pugi::xml_node currentXmlNode = bridgeXmlNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
        {
            if (std::string(uxas::common::StringConstant::SubscribeToMessage().c_str()) == currentXmlNode.name())
            {
                std::string lmcpSubscribeAddress = currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).value();
                if (!lmcpSubscribeAddress.empty())
                {
                    addSubscriptionAddress(lmcpSubscribeAddress);
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

        // do not forward any uni-cast messages addressed to this bridge
        UXAS_LOG_INFORM(s_typeName(), "::configure adding non-forward address [", getNetworkClientUnicastAddress(m_entityId, m_networkId), "]");
        m_nonImportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));
        m_nonExportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));
    }

    return (isSuccess);
};

bool
LmcpObjectNetworkTcpBridge::initialize()
{
    UXAS_LOG_INFORM(s_typeName(), "::initialize - START");
    m_externalLmcpObjectMessageTcpReceiverSenderPipe.initializeStream(m_entityId, m_networkId, m_tcpReceiveSendAddress, m_isServer);
    UXAS_LOG_INFORM(s_typeName(), "::initialize succeeded");
    return (true);
};

bool
LmcpObjectNetworkTcpBridge::start()
{
    m_tcpProcessingThread = uxas::stduxas::make_unique<std::thread>(&LmcpObjectNetworkTcpBridge::executeTcpReceiveProcessing, this);
    UXAS_LOG_INFORM(s_typeName(), "::start TCP receive processing thread [", m_tcpProcessingThread->get_id(), "]");
    return (true);
};

bool
LmcpObjectNetworkTcpBridge::terminate()
{
    m_isTerminate = true;
    if (m_tcpProcessingThread && m_tcpProcessingThread->joinable())
    {
        m_tcpProcessingThread->join();
        UXAS_LOG_INFORM(s_typeName(), "::terminate calling thread completed m_tcpProcessingThread join");
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::terminate unexpectedly could not join m_tcpProcessingThread");
    }
    return (true);
};

bool
LmcpObjectNetworkTcpBridge::processReceivedSerializedLmcpMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> receivedLmcpMessage)
{
    // send message to the external entity
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("LmcpObjectNetworkTcpBridge::processReceivedSerializedLmcpMessage RECEIVED INTERNAL serialized message");
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("Address:          [", receivedLmcpMessage->getAddress(), "]");
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("ContentType:      [", receivedLmcpMessage->getMessageAttributesReference()->getContentType(), "]");
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("Descriptor:       [", receivedLmcpMessage->getMessageAttributesReference()->getDescriptor(), "]");
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("SourceGroup:      [", receivedLmcpMessage->getMessageAttributesReference()->getSourceGroup(), "]");
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("SourceEntityId:   [", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId(), "]");
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("SourceServiceId:  [", receivedLmcpMessage->getMessageAttributesReference()->getSourceServiceId(), "]");
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("AttributesString: [", receivedLmcpMessage->getMessageAttributesReference()->getString(), "]");
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("getPayload:       [", receivedLmcpMessage->getPayload(), "]");
    UXAS_LOG_DEBUG_VERBOSE_BRIDGE("getString:        [", receivedLmcpMessage->getString(), "]");

    // send message to the external entity
    UXAS_LOG_DEBUGGING(s_typeName(), "::processReceivedSerializedLmcpMessage [", m_entityIdNetworkIdUnicastString, 
            "] before processing serialized message having address ", receivedLmcpMessage->getAddress(),
                  " and size ", receivedLmcpMessage->getPayload().size());

    // process messages from a local service (only)
    if (m_entityIdString == receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId())
    {
        if (m_nonExportForwardAddresses.find(receivedLmcpMessage->getAddress()) == m_nonExportForwardAddresses.end())
        {
            UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage processing message with source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId());
            try
            {
                m_externalLmcpObjectMessageTcpReceiverSenderPipe.sendSerializedMessage(std::move(receivedLmcpMessage));
            }
            catch (std::exception& ex)
            {
                UXAS_LOG_ERROR(s_typeName(), "::processReceivedSerializedLmcpMessage failed to process serialized LMCP object; EXCEPTION: ", ex.what());
            }
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
LmcpObjectNetworkTcpBridge::executeTcpReceiveProcessing()
{
    try
    {
        while (!m_isTerminate)
        {
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("LmcpObjectNetworkTcpBridge::executeTcpReceiveProcessing BEFORE calling receivedTcpMessage");
            std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> receivedTcpMessage 
                    = m_externalLmcpObjectMessageTcpReceiverSenderPipe.getNextSerializedMessage();

            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("LmcpObjectNetworkTcpBridge::executeTcpReceiveProcessing RECEIVED EXTERNAL serialized message");
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("Address:          [", receivedTcpMessage->getAddress(), "]");
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("ContentType:      [", receivedTcpMessage->getMessageAttributesReference()->getContentType(), "]");
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("Descriptor:       [", receivedTcpMessage->getMessageAttributesReference()->getDescriptor(), "]");
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("SourceGroup:      [", receivedTcpMessage->getMessageAttributesReference()->getSourceGroup(), "]");
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("SourceEntityId:   [", receivedTcpMessage->getMessageAttributesReference()->getSourceEntityId(), "]");
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("SourceServiceId:  [", receivedTcpMessage->getMessageAttributesReference()->getSourceServiceId(), "]");
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("AttributesString: [", receivedTcpMessage->getMessageAttributesReference()->getString(), "]");
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("getPayload:       [", receivedTcpMessage->getPayload(), "]");
            UXAS_LOG_DEBUG_VERBOSE_BRIDGE("getString:        [", receivedTcpMessage->getString(), "]");

// 20151203 dbk, rjt how much firewall, spam protection is necessary ??
#ifdef IMPACT_BUILD
            // Only allow configurations to be sent out once per session
            // NOTE: this removes the ability to update configurations during run time
            // When AMASE is fixed to not spam configurations, this will no longer be necessary
            static std::unordered_set<int64_t> s_entityConfiguration;
            if (receivedTcpMessage->getDescriptor() == afrl::cmasi::AirVehicleConfiguration::Subscription ||
                    receivedTcpMessage->getDescriptor() == afrl::vehicles::GroundVehicleConfiguration::Subscription ||
                    receivedTcpMessage->getDescriptor() == afrl::vehicles::SurfaceVehicleConfiguration::Subscription)
            {
                // deserialize and create throw-away EntityConfiguration
                std::unique_ptr<avtas::lmcp::Object> lmcpObject = m_externalLmcpObjectMessageReceiverPipe.deserializeMessage(receivedTcpMessage->getPayload());
                afrl::cmasi::EntityConfiguration* entityCfg = static_cast<afrl::cmasi::EntityConfiguration*> (lmcpObject.get());
                auto entityCfgIt = s_entityConfiguration.find(entityCfg->getID());
                if (entityCfgIt == s_entityConfiguration.end())
                {
                    // current configuration not found
                    // send the message along, then put in set for future blocking
                    // process messages from an external service (only)
                    if (m_entityIdString != receivedTcpMessage->getMessageAttributesReference()->getSourceEntityId())
                    {
                        sendSerializedLmcpObjectMessage(std::move(receivedTcpMessage));
                    }
                    else
                    {
                        UXAS_LOG_INFORM(s_typeName(), "::executeSerialReceiveProcessing ignoring external message with entity ID ", m_entityIdString, " since it matches its own entity ID");
                    }
                    s_entityConfiguration.insert(entityCfg->getID());
                }
                else
                {
                    // already received a configuration for this ID and assuming it will not change
                }
            }
            else if (receivedTcpMessage->getDescriptor() == afrl::cmasi::SessionStatus::Subscription ||
                    receivedTcpMessage->getDescriptor() == afrl::cmasi::ServiceStatus::Subscription)
            {
                // block Session Status and Service Status messages
            }
            else
            {
                // send it along
                // process messages from an external service (only)
                if (m_entityIdString != receivedTcpMessage->getMessageAttributesReference()->getSourceEntityId())
                {
                    sendSerializedLmcpObjectMessage(std::move(receivedTcpMessage));
                }
                else
                {
                    UXAS_LOG_INFORM(s_typeName(), "::executeSerialReceiveProcessing ignoring external message with entity ID ", m_entityIdString, " since it matches its own entity ID");
                }
            }
#else
            // process messages from an external service (only)
            if (receivedTcpMessage && (m_entityIdString != receivedTcpMessage->getMessageAttributesReference()->getSourceEntityId()))
            {
                if (m_nonImportForwardAddresses.find(receivedTcpMessage->getAddress()) == m_nonImportForwardAddresses.end())
                {
                    if(m_isConsideredSelfGenerated)
                    {
                        // remove `envelope` and replace with a `broadcast` as if this message
                        // originated with this bridge service
                        
                        // decode message so that `envelope` is auto-created
                        avtas::lmcp::ByteBuffer buf;
                        buf.allocate(receivedTcpMessage->getPayload().size());
                        buf.put((uint8_t*) receivedTcpMessage->getPayload().c_str(), receivedTcpMessage->getPayload().size(), 0);
                        buf.rewind();
                        auto obj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::Factory::getObject(buf));
                        if(obj)
                        {
                            sendSharedLmcpObjectBroadcastMessage(obj);
                        }
                    }
                    else
                    {
                        // send along message with the exact `envelope` as was received
                        sendSerializedLmcpObjectMessage(std::move(receivedTcpMessage));
                    }
                }
                else
                {
                    UXAS_LOG_INFORM(s_typeName(), "::executeTcpReceiveProcessing ignoring non-import message with address ", receivedTcpMessage->getAddress(), ", source entity ID ", receivedTcpMessage->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", receivedTcpMessage->getMessageAttributesReference()->getSourceServiceId());
                }
            }
            else
            {
                UXAS_LOG_INFORM(s_typeName(), "::executeTcpReceiveProcessing ignoring external message with entity ID ", m_entityIdString, " since it matches its own entity ID");
            }
#endif
        }
        UXAS_LOG_INFORM(s_typeName(), "::executeTcpReceiveProcessing exiting infinite loop thread [", std::this_thread::get_id(), "]");
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR(s_typeName(), "::executeTcpReceiveProcessing EXCEPTION: ", ex.what());
    }
};

}; //namespace communications
}; //namespace uxas

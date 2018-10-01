// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectNetworkZeroMqZyreBridge.h"

#include "uxas/messages/uxnative/EntityJoin.h"
#include "uxas/messages/uxnative/EntityExit.h"

#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"

#include "stdUniquePtr.h"

#include "Constants/Constant_Strings.h"
#include "Constants/Constants_Control.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <errno.h>

#if (defined(__APPLE__) && defined(__MACH__))
#define OSX
#endif

#ifdef OSX
#include <unistd.h>
#include <sys/select.h>
#include <termios.h>
#elif (!defined(WIN32))
#include <unistd.h>
#include <sys/select.h>
#include <termio.h>
#endif

#include <cstdint>
#include <functional>
#include <map>
#include <sstream>

namespace uxas
{
namespace communications
{

LmcpObjectNetworkZeroMqZyreBridge::LmcpObjectNetworkZeroMqZyreBridge()
{
};

LmcpObjectNetworkZeroMqZyreBridge::~LmcpObjectNetworkZeroMqZyreBridge()
{
};

bool
LmcpObjectNetworkZeroMqZyreBridge::configure(const pugi::xml_node& bridgeXmlNode)
{
    bool isSuccess{true};

    m_headerKeyValuePairs = uxas::stduxas::make_unique<std::unordered_map<std::string, std::string>>();
    m_headerKeyValuePairs->emplace(uxas::common::StringConstant::EntityID(), m_entityIdString);
    m_headerKeyValuePairs->emplace(uxas::common::StringConstant::EntityType(), m_entityType);
    
    if (!bridgeXmlNode.attribute(uxas::common::StringConstant::GossipBind().c_str()).empty())
    {
        m_isGossipBind = bridgeXmlNode.attribute(uxas::common::StringConstant::GossipBind().c_str()).as_bool();
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::configure reading Zyre gossip bind value ", m_isGossipBind, " from XML configuration");
    }

    if (!bridgeXmlNode.attribute(uxas::common::StringConstant::GossipEndpoint().c_str()).empty())
    {
        m_gossipEndpoint = bridgeXmlNode.attribute(uxas::common::StringConstant::GossipEndpoint().c_str()).value();
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::configure reading Zyre gossip endpoint value ", m_gossipEndpoint, " from XML configuration");
    }

    if (!bridgeXmlNode.attribute(uxas::common::StringConstant::ZyreEndpoint().c_str()).empty() && !m_gossipEndpoint.empty())
    {
        // if this exists, then zyre will use gossip
        m_zyreEndpoint = bridgeXmlNode.attribute(uxas::common::StringConstant::ZyreEndpoint().c_str()).value();
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::configure reading Zyre endpoint value ", m_zyreEndpoint, " from XML configuration");
    }
    else if (!bridgeXmlNode.attribute(uxas::common::StringConstant::NetworkDevice().c_str()).empty())
    {
        m_zyreNetworkDevice = bridgeXmlNode.attribute(uxas::common::StringConstant::NetworkDevice().c_str()).value();
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::configure reading Zyre network device value ", m_zyreNetworkDevice, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::configure setting Zyre network device value to ", m_zyreNetworkDevice, " default value");
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

    std::set<std::string> extSubAddDupChk; // prevent dup external address subscription
    std::string delimitedExtSubAddresses{""};
    for (pugi::xml_node currentXmlNode = bridgeXmlNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
    {
        if (uxas::common::StringConstant::SubscribeToMessage() == currentXmlNode.name())
        {
            std::string messageType = currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).value();
            if (!messageType.empty())
            {
                UXAS_LOG_INFORM(s_typeName(), "::configure adding local subscription address ", messageType);
                addSubscriptionAddress(messageType);
                m_initialPersistentLocalSubscriptionAddresses.emplace(messageType);
            }
        }
        else if (uxas::common::StringConstant::SubscribeToExternalMessage() == currentXmlNode.name())
        {
            std::string messageType = currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).value();
            if (!messageType.empty())
            {
                auto extSubAdd = extSubAddDupChk.find(messageType);
                if (extSubAdd == extSubAddDupChk.end())
                {
                    UXAS_LOG_INFORM(s_typeName(), "::configure adding external subscription address ", messageType);
                    if (delimitedExtSubAddresses.size() > 0)
                    {
                        delimitedExtSubAddresses.append(m_extSubAddressDelimiter);
                    }
                    delimitedExtSubAddresses.append(messageType);
                    extSubAddDupChk.emplace(messageType);
                }
            }
        }
    }

    //
    // DESIGN 20150911 RJT message addressing - entity ID
    // - received/sent LMCP messages always include entity ID
    // - the entity cast address is derived from entity ID (see getEntityCastAddress function)
    // - bridges never subscribe to the entity cast address on the internal network
    // - bridges usually subscribe (or coordinate subscription) to the entity cast address on external networks
    //
    // subscribe to external messages addressed to this entity
    std::string entityCastAddress = getEntityCastAddress(m_entityId);
    auto enCastAdd = extSubAddDupChk.find(entityCastAddress);
    if (enCastAdd == extSubAddDupChk.end())
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure adding external subscription address ", entityCastAddress);
        if (delimitedExtSubAddresses.size() > 0)
        {
            delimitedExtSubAddresses.append(m_extSubAddressDelimiter);
        }
        delimitedExtSubAddresses.append(entityCastAddress);
        extSubAddDupChk.emplace(entityCastAddress);
    }

    // do not forward uni-cast messages addressed to this bridge
    UXAS_LOG_INFORM(s_typeName(), "::configure adding non-forward address [", getNetworkClientUnicastAddress(m_entityId, m_networkId), "]");
    m_nonImportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));
    m_nonExportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));

    m_headerKeyValuePairs->emplace(uxas::common::StringConstant::SubscribeToMessage(), delimitedExtSubAddresses);
 
    m_zeroMqZyreBridge.setZyreEnterMessageHandler(std::bind(&LmcpObjectNetworkZeroMqZyreBridge::zyreEnterMessageHandler, this, std::placeholders::_1, std::placeholders::_2));
    m_zeroMqZyreBridge.setZyreExitMessageHandler(std::bind(&LmcpObjectNetworkZeroMqZyreBridge::zyreExitMessageHandler, this, std::placeholders::_1));
    m_zeroMqZyreBridge.setZyreWhisperMessageHandler(std::bind(&LmcpObjectNetworkZeroMqZyreBridge::zyreWhisperMessageHandler, this, std::placeholders::_1, std::placeholders::_2));

    return (isSuccess);
};

bool
LmcpObjectNetworkZeroMqZyreBridge::start()
{
    return (m_zeroMqZyreBridge.start(m_zyreNetworkDevice, m_zyreEndpoint, m_gossipEndpoint, m_isGossipBind, m_entityIdString, m_headerKeyValuePairs));
};

bool
LmcpObjectNetworkZeroMqZyreBridge::terminate()
{
    return (m_zeroMqZyreBridge.terminate());
};

bool
LmcpObjectNetworkZeroMqZyreBridge::processReceivedSerializedLmcpMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
                                                               receivedLmcpMessage)
{
    //
    // DESIGN 20150911 RJT message addressing - entity ID
    // - received/sent LMCP messages always include entity ID
    // - the entity cast address is derived from entity ID (see getEntityCastAddress function)
    // - bridges never subscribe to the entity cast address on the internal network
    // - bridges usually subscribe (or coordinate subscription) to the entity cast address on external networks

    // messages received from local network
    //1. uni-cast to this bridge - silently ignoring - this is not an valid use case
    //2. uni-cast to external service - look-up UUID based on address subscription map (e.g., e12s14)
    //3. entity multi-cast (less common) - look-up UUID based on address subscription map (e.g., e12)
    //4. topic multi-cast - forward to all external entities that subscribe to the topic address (e.g., roadmonitor)
    //5. broadcast - forward to all external entities based on address subscription (e.g., AirVehicleState)
    //example subscription addresses (for a single entity)
    //e12
    //e12s11
    //e12s12
    //roadmonitor (group)
    //AirVehicleState (content))

    // send message to the external entity
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::processReceivedSerializedLmcpMessage [", m_entityIdNetworkIdUnicastString, 
            "] before processing serialized message having address ", receivedLmcpMessage->getAddress(),
                  " and size ", receivedLmcpMessage->getPayload().size());

    // process messages from a local service (only)
    if (m_entityIdString == receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId())
    {
        if (m_nonExportForwardAddresses.find(receivedLmcpMessage->getAddress()) == m_nonExportForwardAddresses.end())
        {
            UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::processReceivedSerializedLmcpMessage processing message with source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId());
            std::unique_lock<std::mutex> lock(m_mutex);
            std::set<std::string> uuidsSentMsg; // avoid sending message out to an entity more than once
            for (const auto& addressAndUuids : m_remoteZyreUuidsBySubscriptionAddress)
            {
                if (receivedLmcpMessage->getAddress().size() >= addressAndUuids.first.size()
                        && receivedLmcpMessage->getAddress().compare(0, addressAndUuids.first.size(), addressAndUuids.first) == 0)
                {
                    for (const auto& uuid : addressAndUuids.second)
                    {
                        auto uuidIt = uuidsSentMsg.find(uuid);
                        if (uuidIt == uuidsSentMsg.end())
                        {
                            uuidsSentMsg.emplace(uuid);
                            m_zeroMqZyreBridge.sendZyreWhisperMessage(uuid, uxas::common::SentinelSerialBuffer::createSentinelizedString(receivedLmcpMessage->getString()));
                            UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::processReceivedSerializedLmcpMessage sent ", receivedLmcpMessage->getMessageAttributesReference()->getDescriptor(), " message to Zyre UUID ", uuid, " associated with ", m_remoteEntityTypeIdsByZyreUuids[uuid].first, " with ID ", m_remoteEntityTypeIdsByZyreUuids[uuid].second);
                        }
                    }
                }
            }
        }
        else
        {
            UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::processReceivedSerializedLmcpMessage ignoring non-export message with address ", receivedLmcpMessage->getAddress(), ", source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceServiceId());
        }
    }
    else
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::processReceivedSerializedLmcpMessage ignoring message with source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId());
    }
    
    return (false); // always false implies never terminating bridge from here
};

void
LmcpObjectNetworkZeroMqZyreBridge::zyreEnterMessageHandler(const std::string& zyreRemoteUuid, const std::unordered_map<std::string, std::string>& headerKeyValuePairs)
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::zyreEnterMessageHandler - START");
    bool isSuccess{true};
    
    // check validity of input parameters
    std::unique_lock<std::mutex> lock(m_mutex);
    auto entityIdKvPairIt = headerKeyValuePairs.find(uxas::common::StringConstant::EntityID());
    if (entityIdKvPairIt == headerKeyValuePairs.end())
    {
        isSuccess = false;
        UXAS_LOG_ERROR(s_typeName(), "::zyreEnterMessageHandler failed to find the ", uxas::common::StringConstant::EntityID(), " key/value pair in the Zyre header map");
    }
    else if(std::stoull(entityIdKvPairIt->second) == m_entityId)
    {
        isSuccess = false;
        UXAS_LOG_ERROR(s_typeName(), "::zyreEnterMessageHandler self entity ID tried to join [", m_entityId, "]");
    }
    
    auto entityTypeKvPairIt = headerKeyValuePairs.find(uxas::common::StringConstant::EntityType());
    if (entityTypeKvPairIt == headerKeyValuePairs.end())
    {
        isSuccess = false;
        UXAS_LOG_ERROR(s_typeName(), "::zyreEnterMessageHandler failed to find the ", uxas::common::StringConstant::EntityType(), " key/value pair in the Zyre header map");
    }
    
    auto subAddsKvPairIt = headerKeyValuePairs.find(uxas::common::StringConstant::SubscribeToMessage());
    if (subAddsKvPairIt == headerKeyValuePairs.end())
    {
        UXAS_LOG_WARN(s_typeName(), "::zyreEnterMessageHandler failed to find the ", uxas::common::StringConstant::SubscribeToMessage(), " key/value pair in the Zyre header map");
    }
    if (!isSuccess)
    {
        UXAS_LOG_ERROR(s_typeName(), "::zyreEnterMessageHandler failed to process Zyre enter message with UUID ", zyreRemoteUuid);
        return;
    }

    // update subscription addresses and UUIDs
    auto uuidEntityIdPairIt = m_remoteEntityTypeIdsByZyreUuids.find(zyreRemoteUuid);
    if (uuidEntityIdPairIt != m_remoteEntityTypeIdsByZyreUuids.end())
    {
        m_remoteEntityTypeIdsByZyreUuids.erase(uuidEntityIdPairIt);
        UXAS_LOG_WARN(s_typeName(), "::zyreEnterMessageHandler unexpectedly removed existing Zyre UUID/entity ID map pair");
    }
    m_remoteEntityTypeIdsByZyreUuids.emplace(zyreRemoteUuid, std::make_pair(entityTypeKvPairIt->second, entityIdKvPairIt->second));
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::zyreEnterMessageHandler added Zyre UUID ", zyreRemoteUuid, " to entity map for ", entityTypeKvPairIt->second, " with ID ", entityIdKvPairIt->second);

    std::vector<std::string> addresses = uxas::common::StringUtil::split(subAddsKvPairIt->second, *(m_extSubAddressDelimiter.c_str()));
    if (addresses.size() > 0)
    {
        UXAS_LOG_INFORM(s_typeName(), "::zyreEnterMessageHandler processing Zyre enter message having ", addresses.size(), " subscription addresses");
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::zyreEnterMessageHandler processing Zyre enter message having zero subscription addresses");
    }
    
    for (const auto& address : addresses)
    {
        auto addUuidsPairIt = m_remoteZyreUuidsBySubscriptionAddress.find(address);
        if (addUuidsPairIt == m_remoteZyreUuidsBySubscriptionAddress.end())
        {
            addSubscriptionAddress(address);
            m_remoteZyreUuidsBySubscriptionAddress.emplace(address, std::set<std::string>{zyreRemoteUuid});
            UXAS_LOG_INFORM(s_typeName(), "::zyreEnterMessageHandler bridge locally subscribed to address ", address, " mapped to UUID ", zyreRemoteUuid);
        }
        else
        {
            UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::zyreEnterMessageHandler bridge already subscribed to address ", address);
            const auto& uuidIt = addUuidsPairIt->second.find(zyreRemoteUuid);
            if (uuidIt == addUuidsPairIt->second.end())
            {
                addUuidsPairIt->second.emplace(zyreRemoteUuid);
                UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::zyreEnterMessageHandler mapped UUID ", zyreRemoteUuid, ", to address ", address);
            }
            else
            {
                UXAS_LOG_WARN(s_typeName(), "::zyreEnterMessageHandler unexpectedly already contains address [", address, "] UUID [", zyreRemoteUuid, "pair");
            }
        }
    }

    // broadcast entity join message
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::zyreEnterMessageHandler broadcasting EntityJoin for type [", entityTypeKvPairIt->second, "] ID [", entityIdKvPairIt->second, "]");
    std::unique_ptr<uxas::messages::uxnative::EntityJoin> entityJoin = uxas::stduxas::make_unique<uxas::messages::uxnative::EntityJoin>();
    entityJoin->setEntityID(std::stoull(entityIdKvPairIt->second));
    entityJoin->setLabel(entityTypeKvPairIt->second);
    sendLmcpObjectBroadcastMessage(std::move(entityJoin));

    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::zyreEnterMessageHandler - END");
};

void
LmcpObjectNetworkZeroMqZyreBridge::zyreExitMessageHandler(const std::string& zyreRemoteUuid)
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::zyreExitMessageHandler - START");
    std::unique_lock<std::mutex> lock(m_mutex);
    // update subscription addresses and UUIDs
    for (auto addressUuidsIt = m_remoteZyreUuidsBySubscriptionAddress.begin(); addressUuidsIt != m_remoteZyreUuidsBySubscriptionAddress.end();)
    {
        auto uuidIt = addressUuidsIt->second.find(zyreRemoteUuid);
        if (uuidIt != addressUuidsIt->second.end())
        {
            addressUuidsIt->second.erase(uuidIt);
            UXAS_LOG_INFORM(s_typeName(), "::zyreExitMessageHandler removed UUID ", zyreRemoteUuid, " from address [", addressUuidsIt->first, "] in address/UUID map for exiting ", m_remoteEntityTypeIdsByZyreUuids[zyreRemoteUuid].first, " with ID ", m_remoteEntityTypeIdsByZyreUuids[zyreRemoteUuid].second);
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::zyreExitMessageHandler UUID ", zyreRemoteUuid, " was not mapped to address ", addressUuidsIt->first, " (no change to map)");
        }
        
        if (!addressUuidsIt->second.empty())
        {
            addressUuidsIt++;
        }
        else
        {
            auto persisentLocAdd = m_initialPersistentLocalSubscriptionAddresses.find(addressUuidsIt->first);
            if (persisentLocAdd == m_initialPersistentLocalSubscriptionAddresses.end())
            {
                UXAS_LOG_INFORM(s_typeName(), "::zyreExitMessageHandler removing local subscription to address [", addressUuidsIt->first, "]");
                removeSubscriptionAddress(addressUuidsIt->first);
            }
            addressUuidsIt = m_remoteZyreUuidsBySubscriptionAddress.erase(addressUuidsIt);
        }
    }
    
    auto uuidEntityTypeIdPairIt = m_remoteEntityTypeIdsByZyreUuids.find(zyreRemoteUuid);
    if (uuidEntityTypeIdPairIt != m_remoteEntityTypeIdsByZyreUuids.end())
    {
        // broadcast entity exit message
        UXAS_LOG_INFORM(s_typeName(), "::zyreEnterMessageHandler broadcasting EntityExit for type [", uuidEntityTypeIdPairIt->second.first, "] ID [", uuidEntityTypeIdPairIt->second.second, "]");
        std::unique_ptr<uxas::messages::uxnative::EntityExit> entityExit = uxas::stduxas::make_unique<uxas::messages::uxnative::EntityExit>();
        entityExit->setEntityID(std::stoi(uuidEntityTypeIdPairIt->second.second));
        entityExit->setLabel(uuidEntityTypeIdPairIt->second.first);
        sendLmcpObjectBroadcastMessage(std::move(entityExit));
        UXAS_LOG_INFORM(s_typeName(), "::zyreExitMessageHandler removing Zyre UUID ", zyreRemoteUuid, " for ", uuidEntityTypeIdPairIt->second.first, " with ID ", uuidEntityTypeIdPairIt->second.second);
        m_remoteEntityTypeIdsByZyreUuids.erase(uuidEntityTypeIdPairIt);
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::zyreExitMessageHandler unexpectedly did not find (so did not remove) Zyre UUID/entity ID map pair; not sending internal EntityExit message");
    }

    UXAS_LOG_INFORM(s_typeName(), "::zyreExitMessageHandler - END");
};

void
LmcpObjectNetworkZeroMqZyreBridge::zyreWhisperMessageHandler(const std::string& zyreRemoteUuid, const std::string& messagePayload)
{
    if (!messagePayload.empty())
    {
        // DESIGN dbk, rjt: each Zyre whisper message will contain one (and only one), whole LMCP object
        // - only performing a single retrieval from the data buffer
        // - multiple reads from data buffer (via while loop) not implemented
        std::string recvdZyreDataSegment = m_receiveZyreDataBuffer.getNextPayloadString(messagePayload);
        if (!recvdZyreDataSegment.empty())
        {
            UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::zyreWhisperMessageHandler processing received Zyre data string segment");
            std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> recvdAddAttMsg
                    = uxas::stduxas::make_unique<uxas::communications::data::AddressedAttributedMessage>();
            if (recvdAddAttMsg->setAddressAttributesAndPayloadFromDelimitedString(std::move(recvdZyreDataSegment)))
            {
                UXAS_LOG_INFORM(s_typeName(), "::zyreWhisperMessageHandler processing ", recvdAddAttMsg->getMessageAttributesReference()->getDescriptor(),
                           " message from ", m_remoteEntityTypeIdsByZyreUuids[zyreRemoteUuid].first, " with ID ", m_remoteEntityTypeIdsByZyreUuids[zyreRemoteUuid].second);

                // process messages from an external service (only)
                if (m_entityIdString != recvdAddAttMsg->getMessageAttributesReference()->getSourceEntityId())
                {
                    if (m_nonImportForwardAddresses.find(recvdAddAttMsg->getAddress()) == m_nonImportForwardAddresses.end())
                    {
                        if(m_isConsideredSelfGenerated)
                        {
                            recvdAddAttMsg->updateSourceAttributes("ZyreBridge", std::to_string(m_entityId), std::to_string(m_networkId));
                        }
                        sendSerializedLmcpObjectMessage(std::move(recvdAddAttMsg));
                    }
                    else
                    {
                        UXAS_LOG_INFORM(s_typeName(), "::zyreWhisperMessageHandler ignoring non-import message with address ", recvdAddAttMsg->getAddress(), ", source entity ID ", recvdAddAttMsg->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", recvdAddAttMsg->getMessageAttributesReference()->getSourceServiceId());
                    }
                }
                else
                {
                    UXAS_LOG_INFORM(s_typeName(), "::zyreWhisperMessageHandler ignoring external message with entity ID ", m_entityIdString, " since it matches its own entity ID");
                }
            }
            else
            {
                UXAS_LOG_WARN(s_typeName(), "::zyreWhisperMessageHandler failed to create AddressedAttributedMessage object from Zyre data buffer string segment");
            }
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::zyreWhisperMessageHandler data appended to serial buffer, but serial buffer unexpectedly does not contain a complete object string segment");
        }
    }
    else
    {
        try
        {
            UXAS_LOG_WARN(s_typeName(), "::zyreWhisperMessageHandler ignoring external message with empty payload string from ",
                     m_remoteEntityTypeIdsByZyreUuids[zyreRemoteUuid].first, " with ID ", m_remoteEntityTypeIdsByZyreUuids[zyreRemoteUuid].second);
        }
        catch (std::exception& ex)
        {
            UXAS_LOG_ERROR(s_typeName(), "::zyreWhisperMessageHandler EXCEPTION: ", ex.what());
        }
    }
};

}; //namespace communications
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectNetworkClientBase.h"

#include "avtas/lmcp/ByteBuffer.h"
#include "avtas/lmcp/Factory.h"
#include "uxas/messages/uxnative/KillService.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"

#include "stdUniquePtr.h"

namespace uxas
{
namespace communications
{

int64_t LmcpObjectNetworkClientBase::s_uniqueEntitySendMessageId = {1};

std::string LmcpObjectNetworkClientBase::s_entityServicesCastAllAddress 
        = getEntityServicesCastAllAddress(uxas::common::ConfigurationManager::getInstance().getEntityId());
    
uint32_t LmcpObjectNetworkClientBase::s_nextNetworkClientId = {10};

LmcpObjectNetworkClientBase::LmcpObjectNetworkClientBase()
{
    m_networkId = s_nextNetworkClientId++;
    m_networkIdString = std::to_string(m_networkId);
    LOG_INFORM("LmcpObjectNetworkClientBase initializing LMCP network ID ", m_networkId);
};

LmcpObjectNetworkClientBase::~LmcpObjectNetworkClientBase()
{
    if (m_networkClientThread && m_networkClientThread->joinable())
    {
        m_networkClientThread->detach();
    }
};

bool
LmcpObjectNetworkClientBase::configureNetworkClient(const std::string& subclassTypeName, ReceiveProcessingType receiveProcessingType, const pugi::xml_node& networkClientXmlNode)
{
    LOG_DEBUGGING("LmcpObjectNetworkClientBase::configureNetworkClient method START");
    m_entityId = uxas::common::ConfigurationManager::getInstance().getEntityId();
    m_entityIdString = std::to_string(m_entityId);
    m_entityType = uxas::common::ConfigurationManager::getInstance().getEntityType();
    m_networkClientTypeName = subclassTypeName;
    m_receiveProcessingType = receiveProcessingType;

    //
    // DESIGN 20150911 RJT message addressing - entity ID + service ID (uni-cast)
    // - sent messages always include entity ID and service ID
    // - the network client uni-cast address is derived from entity ID and service ID (see getNetworkClientUnicastAddress function)
    // - network clients always subscribe to the entity ID + service ID uni-cast address on the internal network
    // - bridges never subscribe to the entity ID + service ID uni-cast address on an external network (since already subscribing to the entity cast address)
    //
    // subscribe to messages addressed to network client (bridge, service, etc.)
    m_entityIdNetworkIdUnicastString = getNetworkClientUnicastAddress(m_entityId, m_networkId);
    LOG_INFORM(m_networkClientTypeName, "::configureNetworkClient subscribing to service uni-cast address [", m_entityIdNetworkIdUnicastString, "]");
    addSubscriptionAddress(m_entityIdNetworkIdUnicastString);
    s_entityServicesCastAllAddress = getEntityServicesCastAllAddress(m_entityId);
    LOG_INFORM(m_networkClientTypeName, "::configureNetworkClient subscribing to entity cast-to-all services address [", s_entityServicesCastAllAddress, "]");
    addSubscriptionAddress(s_entityServicesCastAllAddress);
    
    // network client can be terminated via received KillService message
    addSubscriptionAddress(uxas::messages::uxnative::KillService::Subscription);

#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_MESSAGING
    std::stringstream xmlNd{""};
    networkClientXmlNode.print(xmlNd);
    LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::configureNetworkClient calling configure - passing XML ", xmlNd.str());
#endif
    m_isConfigured = configure(networkClientXmlNode);

    if (m_isConfigured)
    {
        LOG_INFORM(m_networkClientTypeName, "::configureNetworkClient configure call succeeded");
    }
    else
    {
        LOG_ERROR(m_networkClientTypeName, "::configureNetworkClient configure call failed");
    }

    LOG_DEBUGGING(m_networkClientTypeName, "::configureNetworkClient method END");
    return (m_isConfigured);
};

bool
LmcpObjectNetworkClientBase::initializeAndStart()
{
    LOG_DEBUGGING(m_networkClientTypeName, "::initializeAndStart method START");

    if (m_isConfigured)
    {
        LOG_INFORM(m_networkClientTypeName, "::initializeAndStart started since configureNetworkClient has been called");
    }
    else
    {
        LOG_ERROR(m_networkClientTypeName, "::initializeAndStart failed - must invoke configureNetworkClient method BEFORE calling initializeAndStart");
        return (false);
    }

    if (initializeNetworkClient())
    {
        LOG_INFORM(m_networkClientTypeName, "::initializeAndStart initializeNetworkClient call succeeded");
    }
    else
    {
        LOG_ERROR(m_networkClientTypeName, "::initializeAndStart initializeNetworkClient call failed");
        return (false);
    }

    if (initialize())
    {
        LOG_INFORM(m_networkClientTypeName, "::initializeAndStart initialize call succeeded");
    }
    else
    {
        LOG_ERROR(m_networkClientTypeName, "::initializeAndStart initialize call failed");
        return (false);
    }

    if (start())
    {
        LOG_INFORM(m_networkClientTypeName, "::initializeAndStart start call succeeded");
    }
    else
    {
        LOG_ERROR(m_networkClientTypeName, "::initializeAndStart start call failed");
        return (false);
    }

    LOG_INFORM(m_networkClientTypeName, "::initializeAndStart processing thread starting ...");
    switch (m_receiveProcessingType)
    {
        case ReceiveProcessingType::LMCP:
            m_networkClientThread = uxas::stduxas::make_unique<std::thread>(&LmcpObjectNetworkClientBase::executeNetworkClient, this);
            LOG_INFORM(m_networkClientTypeName, "::initializeAndStart started LMCP network client processing thread [", m_networkClientThread->get_id(), "]");
            break;
        case ReceiveProcessingType::SERIALIZED_LMCP:
            m_networkClientThread = uxas::stduxas::make_unique<std::thread>(&LmcpObjectNetworkClientBase::executeSerializedNetworkClient, this);
            LOG_INFORM(m_networkClientTypeName, "::initializeAndStart started LMCP network client serialized processing thread [", m_networkClientThread->get_id(), "]");
            break;
        default:
            LOG_ERROR(m_networkClientTypeName, "::initializeAndStart failed to initialize LMCP network client processing thread; un-handled ReceiveProcessingType case");
    }

    LOG_INFORM(m_networkClientTypeName, "::initializeAndStart processing thread started");

    LOG_DEBUGGING(m_networkClientTypeName, "::initializeAndStart method END");
    return (true);
};

bool
LmcpObjectNetworkClientBase::addSubscriptionAddress(const std::string& address)
{
    LOG_DEBUGGING(m_networkClientTypeName, "::addSubscriptionAddress method START");
    bool isAdded{false};
    if (m_isThreadStarted)
    {
        if (m_lmcpObjectMessageReceiverPipe.addLmcpObjectSubscriptionAddress(address))
        {
            LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress subscribed to message address [", address, "]");
        }
        else
        {
            LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress attempted to subscribe to message address [", address, "] "
                       " subscription not added since already exists");
        }
    }
    else
    {
        if (m_preStartLmcpSubscriptionAddresses.emplace(address).second)
        {
            LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress staged subscribe address [", address, "]");
        }
        else
        {
            LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress attempted to stage subscribe address  [", address, "] "
                       " subscription not added since already staged");
        }
    }

    LOG_DEBUGGING(m_networkClientTypeName, "::addSubscriptionAddress method END");
    return (true);
};

bool
LmcpObjectNetworkClientBase::removeSubscriptionAddress(const std::string& address)
{
    bool isRemoved{false};
    if (m_isThreadStarted)
    {
        isRemoved = m_lmcpObjectMessageReceiverPipe.removeLmcpObjectSubscriptionAddress(address);
    }
    else
    {
        isRemoved = ((m_preStartLmcpSubscriptionAddresses.erase(address) > 0) ? true : false);
    }

    if (isRemoved)
    {
        LOG_INFORM(m_networkClientTypeName, "::removeSubscriptionAddress unsubscribed to LMCP message address [", address, "]");
    }
    else
    {
        LOG_INFORM(m_networkClientTypeName, "::removeSubscriptionAddress attempted to unsubscribe to LMCP message address [", address, "] "
                   " subscription not removed since did not exist");
    }

    return false;
};

bool
LmcpObjectNetworkClientBase::removeAllSubscriptionAddresses()
{
    bool isRemoved{false};
    if (m_isThreadStarted)
    {
        isRemoved = m_lmcpObjectMessageReceiverPipe.removeAllLmcpObjectSubscriptionAddresses();
    }
    else
    {
        m_preStartLmcpSubscriptionAddresses.clear();
        isRemoved = true;
    }

    if (isRemoved)
    {
        LOG_INFORM(m_networkClientTypeName, "::removeAllSubscriptionAddresses unsubscribed to all LMCP message addresses");
    }
    else
    {
        LOG_INFORM(m_networkClientTypeName, "::removeAllSubscriptionAddresses cleared all pre-start LMCP message addresses");
    }

    return false;
};

bool
LmcpObjectNetworkClientBase::initializeNetworkClient()
{
    LOG_DEBUGGING(m_networkClientTypeName, "::initializeNetworkClient method START");

    m_lmcpObjectMessageReceiverPipe.initializeSubscription(m_entityId, m_networkId);

    for (const auto& address : m_preStartLmcpSubscriptionAddresses)
    {
        if (m_lmcpObjectMessageReceiverPipe.addLmcpObjectSubscriptionAddress(address))
        {
            LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress subscribed to staged message address [", address, "]");
        }
        else
        {
            LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress attempted to subscribe to staged message address [", address, "] "
                       " subscription not added since already exists");
        }
    }

    m_lmcpObjectMessageSenderPipe.initializePush(m_messageSourceGroup, m_entityId, m_networkId);

    LOG_DEBUGGING(m_networkClientTypeName, "::initializesendAddressedAttributedMessageNetworkClient method END");
    return (true);
};

void
LmcpObjectNetworkClientBase::executeNetworkClient()
{
    try
    {
        LOG_DEBUGGING(m_networkClientTypeName, "::executeNetworkClient method START");
        LOG_DEBUGGING(m_networkClientTypeName, "::executeNetworkClient method START infinite while loop");
        m_isThreadStarted = true;
        while (!m_isTerminateNetworkClient)
        {
            try
            {
                // get the next LMCP message (if any) from the LMCP network server
                LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::executeNetworkClient calling m_lmcpObjectMessageReceiverPipe.getNextMessageObject()");
                std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage
                        = m_lmcpObjectMessageReceiverPipe.getNextMessageObject();
                LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::executeNetworkClient completed calling m_lmcpObjectMessageReceiverPipe.getNextMessageObject()");

                if (receivedLmcpMessage)
                {
                    LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::executeNetworkClient processing received LMCP message");
                    LOG_DEBUG_VERBOSE_MESSAGING("ContentType:      [", receivedLmcpMessage->m_attributes->getContentType(), "]");
                    LOG_DEBUG_VERBOSE_MESSAGING("Descriptor:       [", receivedLmcpMessage->m_attributes->getDescriptor(), "]");
                    LOG_DEBUG_VERBOSE_MESSAGING("SourceGroup:      [", receivedLmcpMessage->m_attributes->getSourceGroup(), "]");
                    LOG_DEBUG_VERBOSE_MESSAGING("SourceEntityId:   [", receivedLmcpMessage->m_attributes->getSourceEntityId(), "]");
                    LOG_DEBUG_VERBOSE_MESSAGING("SourceServiceId:  [", receivedLmcpMessage->m_attributes->getSourceServiceId(), "]");
                    LOG_DEBUG_VERBOSE_MESSAGING("AttributesString: [", receivedLmcpMessage->m_attributes->getString(), "]");
                    if ((m_isBaseClassKillServiceProcessingPermitted
                            && uxas::messages::uxnative::isKillService(receivedLmcpMessage->m_object)
                            //&& m_entityIdString.compare(std::static_pointer_cast<uxas::messages::uxnative::KillService>(receivedLmcpMessage->m_object)->getEntityID()) == 0//TODO check entityID
                            && m_networkIdString.compare(std::to_string(std::static_pointer_cast<uxas::messages::uxnative::KillService>(receivedLmcpMessage->m_object)->getServiceID())) == 0)
                            || processReceivedLmcpMessage(std::move(receivedLmcpMessage)))
                    {
                        LOG_INFORM(m_networkClientTypeName, "::executeNetworkClient starting termination since received [", uxas::messages::uxnative::KillService::TypeName, "] message ");
                        m_isTerminateNetworkClient = true;
                    }
                }
            }
            catch (std::exception& ex)
            {
                LOG_ERROR(m_networkClientTypeName, "::executeNetworkClient continuing infinite while loop after EXCEPTION: ", ex.what());
            }
        }
        
        LOG_DEBUGGING(m_networkClientTypeName, "::executeNetworkClient method END infinite while loop");

        m_isBaseClassTerminationFinished = true;

        uint32_t subclassTerminateDuration_ms{0};
        while (true)
        {
            m_isSubclassTerminationFinished = terminate();
            if (m_isSubclassTerminationFinished)
            {
                LOG_INFORM(m_networkClientTypeName, "::executeNetworkClient terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
                break;
            }

            std::this_thread::sleep_for(std::chrono::milliseconds(m_subclassTerminationAttemptPeriod_ms));
            subclassTerminateDuration_ms += m_subclassTerminationAttemptPeriod_ms;
            if (subclassTerminateDuration_ms > m_subclassTerminationWarnDuration_ms)
            {
                LOG_WARN(m_networkClientTypeName, "::executeNetworkClient has not terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
            }
            else if (subclassTerminateDuration_ms > m_subclassTerminationAbortDuration_ms)
            {
                LOG_ERROR(m_networkClientTypeName, "::executeNetworkClient aborting termination of subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
                break;
            }
        }
        LOG_INFORM(m_networkClientTypeName, "::executeNetworkClient exiting infinite loop thread [", std::this_thread::get_id(), "]");
        LOG_DEBUGGING(m_networkClientTypeName, "::executeNetworkClient method END");
    }
    catch (std::exception& ex)
    {
        LOG_ERROR(m_networkClientTypeName, "::executeNetworkClient EXCEPTION: ", ex.what());
    }
};

void
LmcpObjectNetworkClientBase::executeSerializedNetworkClient()
{
    try
    {
        LOG_DEBUGGING(m_networkClientTypeName, "::executeSerializedNetworkClient method START");
        LOG_DEBUGGING(m_networkClientTypeName, "::executeSerializedNetworkClient method START infinite while loop");
        m_isThreadStarted = true;
        while (!m_isTerminateNetworkClient)
        {
            // get the next serialized LMCP object message (if any) from the LMCP network server
            std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
                    nextReceivedSerializedLmcpObject
                    = m_lmcpObjectMessageReceiverPipe.getNextSerializedMessage();

            if (nextReceivedSerializedLmcpObject)
            {
                LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::executeSerializedNetworkClient processing received LMCP message");
                LOG_DEBUG_VERBOSE_MESSAGING("Address:          [", nextReceivedSerializedLmcpObject->getAddress(), "]");
                LOG_DEBUG_VERBOSE_MESSAGING("ContentType:      [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getContentType(), "]");
                LOG_DEBUG_VERBOSE_MESSAGING("Descriptor:       [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getDescriptor(), "]");
                LOG_DEBUG_VERBOSE_MESSAGING("SourceGroup:      [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getSourceGroup(), "]");
                LOG_DEBUG_VERBOSE_MESSAGING("SourceEntityId:   [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getSourceEntityId(), "]");
                LOG_DEBUG_VERBOSE_MESSAGING("SourceServiceId:  [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getSourceServiceId(), "]");
                LOG_DEBUG_VERBOSE_MESSAGING("AttributesString: [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getString(), "]");
                LOG_DEBUG_VERBOSE_MESSAGING("getPayload:       [", nextReceivedSerializedLmcpObject->getPayload(), "]");
                LOG_DEBUG_VERBOSE_MESSAGING("getString:        [", nextReceivedSerializedLmcpObject->getString(), "]");

                if (m_isBaseClassKillServiceProcessingPermitted
                        && nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getDescriptor()
                        .rfind(uxas::messages::uxnative::KillService::Subscription) != std::string::npos)
                {
                    // reconstitute LMCP object
                    std::shared_ptr<avtas::lmcp::Object> lmcpObject = deserializeMessage(nextReceivedSerializedLmcpObject->getPayload());
                    // check KillService serviceID == my serviceID
                    if (uxas::messages::uxnative::isKillService(lmcpObject)
                            //&& m_entityIdString.compare(std::static_pointer_cast<uxas::messages::uxnative::KillService>(lmcpObject)->getEntityID()) == 0//TODO check entityID
                            && m_networkIdString.compare(std::to_string(std::static_pointer_cast<uxas::messages::uxnative::KillService>(lmcpObject)->getServiceID())) == 0)
                    {
                        LOG_INFORM(m_networkClientTypeName, "::executeSerializedNetworkClient starting termination since received [", uxas::messages::uxnative::KillService::TypeName, "] message ");
                        m_isTerminateNetworkClient = true;
                    }
                }
                else if (processReceivedSerializedLmcpMessage(std::move(nextReceivedSerializedLmcpObject)))
                {
                    m_isTerminateNetworkClient = true;
                }
            }
        }

        LOG_DEBUGGING(m_networkClientTypeName, "::executeSerializedNetworkClient method END infinite while loop");
        
        m_isBaseClassTerminationFinished = true;

        uint32_t subclassTerminateDuration_ms{0};
        while (true)
        {
            m_isSubclassTerminationFinished = terminate();
            if (m_isSubclassTerminationFinished)
            {
                LOG_INFORM(m_networkClientTypeName, "::executeSerializedNetworkClient terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
                break;
            }
            
            std::this_thread::sleep_for(std::chrono::milliseconds(m_subclassTerminationAttemptPeriod_ms));
            subclassTerminateDuration_ms += m_subclassTerminationAttemptPeriod_ms;
            if (subclassTerminateDuration_ms > m_subclassTerminationWarnDuration_ms)
            {
                LOG_WARN(m_networkClientTypeName, "::executeSerializedNetworkClient has not terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
            }
            else if (subclassTerminateDuration_ms > m_subclassTerminationAbortDuration_ms)
            {
                LOG_ERROR(m_networkClientTypeName, "::executeSerializedNetworkClient aborting termination of subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
                m_isSubclassTerminationFinished = true;
                break;
            }
        }
        LOG_INFORM(m_networkClientTypeName, "::executeSerializedNetworkClient exiting infinite loop thread [", std::this_thread::get_id(), "]");
        LOG_DEBUGGING(m_networkClientTypeName, "::executeSerializedNetworkClient method END");
    }
    catch (std::exception& ex)
    {
        LOG_ERROR(m_networkClientTypeName, "::executeSerializedNetworkClient EXCEPTION: ", ex.what());
    }
};

std::shared_ptr<avtas::lmcp::Object>
LmcpObjectNetworkClientBase::deserializeMessage(const std::string& payload)
{
    std::shared_ptr<avtas::lmcp::Object> lmcpObject;

    // allocate memory
    avtas::lmcp::ByteBuffer lmcpByteBuffer;
    lmcpByteBuffer.allocate(payload.size());
    lmcpByteBuffer.rewind();

    for (int32_t charIndex = 0; charIndex < payload.size(); charIndex++)
    {
        lmcpByteBuffer.putByte(payload[charIndex]); // TODO REVIEW
    }
    lmcpByteBuffer.rewind();
    
    lmcpObject.reset(avtas::lmcp::Factory::getObject(lmcpByteBuffer));
    if (!lmcpObject)
    {
        LOG_ERROR("LmcpObjectMessageReceiverPipe::deserializeMessage failed to convert message payload string into an LMCP object");
    }

    return (lmcpObject);
};

void
LmcpObjectNetworkClientBase::sendLmcpObjectBroadcastMessage(std::unique_ptr<avtas::lmcp::Object> lmcpObject)
{
    s_uniqueEntitySendMessageId++;
    m_lmcpObjectMessageSenderPipe.sendBroadcastMessage(std::move(lmcpObject));
};

void
LmcpObjectNetworkClientBase::sendLmcpObjectLimitedCastMessage(const std::string& castAddress, std::unique_ptr<avtas::lmcp::Object> lmcpObject)
{
    s_uniqueEntitySendMessageId++;
    m_lmcpObjectMessageSenderPipe.sendLimitedCastMessage(castAddress, std::move(lmcpObject));
};

void
LmcpObjectNetworkClientBase::sendSerializedLmcpObjectMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> serializedLmcpObject)
{
    s_uniqueEntitySendMessageId++;
    m_lmcpObjectMessageSenderPipe.sendSerializedMessage(std::move(serializedLmcpObject));
};

void
LmcpObjectNetworkClientBase::sendSharedLmcpObjectBroadcastMessage(const std::shared_ptr<avtas::lmcp::Object>& lmcpObject)
{
    s_uniqueEntitySendMessageId++;
    m_lmcpObjectMessageSenderPipe.sendSharedBroadcastMessage(lmcpObject);
};

void
LmcpObjectNetworkClientBase::sendSharedLmcpObjectLimitedCastMessage(const std::string& castAddress, const std::shared_ptr<avtas::lmcp::Object>& lmcpObject)
{
    s_uniqueEntitySendMessageId++;
    m_lmcpObjectMessageSenderPipe.sendSharedLimitedCastMessage(castAddress, lmcpObject);
};

}; //namespace communications
}; //namespace uxas

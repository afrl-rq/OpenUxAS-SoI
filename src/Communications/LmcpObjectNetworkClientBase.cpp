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

/**
 * ZSRM includes
 */
extern "C" {
#include <zsrmvapi.h>
}

namespace
{
    void zs_budget_enforcement_helper(void *param, int rid)
    {
        if (param != NULL)
        {
            try
            {
                uxas::communications::LmcpObjectNetworkClientBase &obj = *(static_cast<uxas::communications::LmcpObjectNetworkClientBase *>(param));
                obj.zs_budget_enforcement_handler(rid);
            }
            catch (std::exception& ex)
            {
                 std::cout << "zs_budget_enforcement_helper() exception: " << ex.what() << "\n";
            }
       }
    }
}

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
    UXAS_LOG_INFORM("LmcpObjectNetworkClientBase initializing LMCP network ID ", m_networkId);
};

LmcpObjectNetworkClientBase::~LmcpObjectNetworkClientBase()
{
    if (m_networkClientThread && m_networkClientThread->joinable())
    {
        m_networkClientThread->detach();
    }

    if (zs_isReservationEnabled){
        if (zsv_delete_reserve(zs_schedfd, zs_rid) <0){
            std::cout << "Failed to delete reserve\n";
        }
    
        if (zsv_close_scheduler(zs_schedfd) <0){
            std::cout << "Failed to close the scheduler\n";
        }
    }
};

bool
LmcpObjectNetworkClientBase::configureNetworkClient(const std::string& subclassTypeName, ReceiveProcessingType receiveProcessingType, const pugi::xml_node& networkClientXmlNode)
{
    UXAS_LOG_DEBUGGING("LmcpObjectNetworkClientBase::configureNetworkClient method START");
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
    UXAS_LOG_INFORM(m_networkClientTypeName, "::configureNetworkClient subscribing to service uni-cast address [", m_entityIdNetworkIdUnicastString, "]");
    addSubscriptionAddress(m_entityIdNetworkIdUnicastString);
    s_entityServicesCastAllAddress = getEntityServicesCastAllAddress(m_entityId);
    UXAS_LOG_INFORM(m_networkClientTypeName, "::configureNetworkClient subscribing to entity cast-to-all services address [", s_entityServicesCastAllAddress, "]");
    addSubscriptionAddress(s_entityServicesCastAllAddress);
    
    // network client can be terminated via received KillService message
    addSubscriptionAddress(uxas::messages::uxnative::KillService::Subscription);

#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_MESSAGING
    std::stringstream xmlNd{""};
    networkClientXmlNode.print(xmlNd);
    UXAS_LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::configureNetworkClient calling configure - passing XML ", xmlNd.str());
#endif
    m_isConfigured = configure(networkClientXmlNode);

    if (m_isConfigured)
    {
        UXAS_LOG_INFORM(m_networkClientTypeName, "::configureNetworkClient configure call succeeded");
    }
    else
    {
        UXAS_LOG_ERROR(m_networkClientTypeName, "::configureNetworkClient configure call failed");
    }

    UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::configureNetworkClient method END");
    return (m_isConfigured);
};

bool
LmcpObjectNetworkClientBase::initializeAndStart()
{
    UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::initializeAndStart method START");

    if (m_isConfigured)
    {
        UXAS_LOG_INFORM(m_networkClientTypeName, "::initializeAndStart started since configureNetworkClient has been called");
    }
    else
    {
        UXAS_LOG_ERROR(m_networkClientTypeName, "::initializeAndStart failed - must invoke configureNetworkClient method BEFORE calling initializeAndStart");
        return (false);
    }

    if (initializeNetworkClient())
    {
        UXAS_LOG_INFORM(m_networkClientTypeName, "::initializeAndStart initializeNetworkClient call succeeded");
    }
    else
    {
        UXAS_LOG_ERROR(m_networkClientTypeName, "::initializeAndStart initializeNetworkClient call failed");
        return (false);
    }

    if (initialize())
    {
        UXAS_LOG_INFORM(m_networkClientTypeName, "::initializeAndStart initialize call succeeded");
    }
    else
    {
        UXAS_LOG_ERROR(m_networkClientTypeName, "::initializeAndStart initialize call failed");
        return (false);
    }

    if (start())
    {
        UXAS_LOG_INFORM(m_networkClientTypeName, "::initializeAndStart start call succeeded");
    }
    else
    {
        UXAS_LOG_ERROR(m_networkClientTypeName, "::initializeAndStart start call failed");
        return (false);
    }

    UXAS_LOG_INFORM(m_networkClientTypeName, "::initializeAndStart processing thread starting ...");
    switch (m_receiveProcessingType)
    {
        case ReceiveProcessingType::LMCP:
            m_networkClientThread = uxas::stduxas::make_unique<std::thread>(&LmcpObjectNetworkClientBase::executeNetworkClient, this);
            UXAS_LOG_INFORM(m_networkClientTypeName, "::initializeAndStart started LMCP network client processing thread [", m_networkClientThread->get_id(), "]");
            break;
        case ReceiveProcessingType::SERIALIZED_LMCP:
            m_networkClientThread = uxas::stduxas::make_unique<std::thread>(&LmcpObjectNetworkClientBase::executeSerializedNetworkClient, this);
            UXAS_LOG_INFORM(m_networkClientTypeName, "::initializeAndStart started LMCP network client serialized processing thread [", m_networkClientThread->get_id(), "]");
            break;
        default:
            UXAS_LOG_ERROR(m_networkClientTypeName, "::initializeAndStart failed to initialize LMCP network client processing thread; un-handled ReceiveProcessingType case");
    }

    UXAS_LOG_INFORM(m_networkClientTypeName, "::initializeAndStart processing thread started");

    UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::initializeAndStart method END");
    return (true);
};

bool
LmcpObjectNetworkClientBase::addSubscriptionAddress(const std::string& address)
{
    UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::addSubscriptionAddress method START");
    bool isAdded{false};
    if (m_isThreadStarted)
    {
        if (m_lmcpObjectMessageReceiverPipe.addLmcpObjectSubscriptionAddress(address))
        {
            UXAS_LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress subscribed to message address [", address, "]");
        }
        else
        {
            UXAS_LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress attempted to subscribe to message address [", address, "] "
                       " subscription not added since already exists");
        }
    }
    else
    {
        if (m_preStartLmcpSubscriptionAddresses.emplace(address).second)
        {
            UXAS_LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress staged subscribe address [", address, "]");
        }
        else
        {
            UXAS_LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress attempted to stage subscribe address  [", address, "] "
                       " subscription not added since already staged");
        }
    }

    UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::addSubscriptionAddress method END");
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
        UXAS_LOG_INFORM(m_networkClientTypeName, "::removeSubscriptionAddress unsubscribed to LMCP message address [", address, "]");
    }
    else
    {
        UXAS_LOG_INFORM(m_networkClientTypeName, "::removeSubscriptionAddress attempted to unsubscribe to LMCP message address [", address, "] "
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
        UXAS_LOG_INFORM(m_networkClientTypeName, "::removeAllSubscriptionAddresses unsubscribed to all LMCP message addresses");
    }
    else
    {
        UXAS_LOG_INFORM(m_networkClientTypeName, "::removeAllSubscriptionAddresses cleared all pre-start LMCP message addresses");
    }

    return false;
};

bool
LmcpObjectNetworkClientBase::initializeNetworkClient()
{
    UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::initializeNetworkClient method START");

    m_lmcpObjectMessageReceiverPipe.initializeSubscription(m_entityId, m_networkId);

    for (const auto& address : m_preStartLmcpSubscriptionAddresses)
    {
        if (m_lmcpObjectMessageReceiverPipe.addLmcpObjectSubscriptionAddress(address))
        {
            UXAS_LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress subscribed to staged message address [", address, "]");
        }
        else
        {
            UXAS_LOG_INFORM(m_networkClientTypeName, "::addSubscriptionAddress attempted to subscribe to staged message address [", address, "] "
                       " subscription not added since already exists");
        }
    }

    m_lmcpObjectMessageSenderPipe.initializePush(m_messageSourceGroup, m_entityId, m_networkId);

    UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::initializesendAddressedAttributedMessageNetworkClient method END");
    
    /**
     * ZSRM calls
     * 
     */
    if (zs_isReservationEnabled){
        if ((zs_schedfd = zsv_open_scheduler())<0){
            std::cout << "Error opening the scheduler\n";
        }

    
        if ((zs_rid = zsv_create_reserve(zs_schedfd,
				zs_period_secs, // period_secs
				zs_period_nsecs, // period_nsecs
				zs_zero_slack_secs, // zsinstant_sec -- same as period = disabled
				zs_zero_slack_nsecs, // zsinstant_nsec -- same as period = disabled
				zs_overload_wcet_secs, // exectime _secs
				zs_overload_wcet_nsecs, // exectime_nsecs
				zs_nominal_wcet_secs, // nominal_exectime_sec -- same as overloaded
				zs_nominal_wcet_nsecs, // nominal_exectime_nsec -- same as overloaded
				1, // priority -- will be changed internally so setting it to 1 is enough
				zs_criticality  // criticality
				))<0){
            std::cout << "error calling create reserve\n";
        }

        if (zsv_fork_enforcement_handler(zs_schedfd,zs_rid,zs_budget_enforcement_helper,this)<0){
            std::cout << "::initializesendAddressedAttributedMessageNetworkClient method COULD NOT REGISTER budget enforcement handler helper\n" ;
        }
    }
    
    return (true);
};

void
LmcpObjectNetworkClientBase::executeNetworkClient()
{
    try
    {
        UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::executeNetworkClient method START");
        UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::executeNetworkClient method START infinite while loop");
        m_isThreadStarted = true;

        // ZSRM debug
        std::cout << "Started tid(" << gettid() << ")\n";

        while (!m_isTerminateNetworkClient)
        {
            try
            {
                // The first time we do not call wait for period but let the task wait for the first 
                // message, this way we "sync" the wait for next period with the message sender
                if (zs_isReservationEnabled && zs_isReserveAttached){
                    //std::cout << "Calling end_period tid("<< gettid() << ") rid(" << zs_rid << ")\n" ;
                    zsv_end_period(zs_schedfd,zs_rid);
                    //zsv_wait_period(zs_schedfd,zs_rid);
                }
                // get the next LMCP message (if any) from the LMCP network server
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::executeNetworkClient calling m_lmcpObjectMessageReceiverPipe.getNextMessageObject()");
                std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage;
                // ZSRM: loop while we keep being enforced
                bool zsInterruptionException =false;
                do {
                    zsInterruptionException = false;
                    try
                    {
                        //std::unique_ptr<uxas::communications::data::LmcpMessage> 
                        receivedLmcpMessage
                            = m_lmcpObjectMessageReceiverPipe.getNextMessageObject();
                    } 
                    catch (std::exception& intrException)
                    {
                        std::string exName = std::string(intrException.what());
//                        if (exName == "Interrupted system call"){
//                            zsInterruptionException = true;
//                        } else {
//                            // not the exception we are interested in
//                            // keep propagating
//                            throw intrException;
//                        }
                        zsInterruptionException = true;
                    }
                } while (zsInterruptionException);
                if (zs_isReservationEnabled){
                    if (!zs_isReserveAttached){
                        // attach it for the first time
                        if (zsv_attach_reserve(zs_schedfd, gettid(), zs_rid)<0){
                          std::cout << "Error attaching the reserve \n";
                        }
                        zs_isReserveAttached = true;
                        std::cout << "Attached reserved rid("<<zs_rid<<") to tid(" << gettid() << ")\n";
                    } else {
                        //std::cout << "Calling wait_release tid("<< gettid() << ") rid(" << zs_rid << ")\n" ;    
                        zsv_wait_release(zs_schedfd,zs_rid);
                    }
                }
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::executeNetworkClient completed calling m_lmcpObjectMessageReceiverPipe.getNextMessageObject()");

                if (receivedLmcpMessage)
                {
                    UXAS_LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::executeNetworkClient processing received LMCP message");
                    UXAS_LOG_DEBUG_VERBOSE_MESSAGING("ContentType:      [", receivedLmcpMessage->m_attributes->getContentType(), "]");
                    UXAS_LOG_DEBUG_VERBOSE_MESSAGING("Descriptor:       [", receivedLmcpMessage->m_attributes->getDescriptor(), "]");
                    UXAS_LOG_DEBUG_VERBOSE_MESSAGING("SourceGroup:      [", receivedLmcpMessage->m_attributes->getSourceGroup(), "]");
                    UXAS_LOG_DEBUG_VERBOSE_MESSAGING("SourceEntityId:   [", receivedLmcpMessage->m_attributes->getSourceEntityId(), "]");
                    UXAS_LOG_DEBUG_VERBOSE_MESSAGING("SourceServiceId:  [", receivedLmcpMessage->m_attributes->getSourceServiceId(), "]");
                    UXAS_LOG_DEBUG_VERBOSE_MESSAGING("AttributesString: [", receivedLmcpMessage->m_attributes->getString(), "]");
                    if ((m_isBaseClassKillServiceProcessingPermitted
                            && uxas::messages::uxnative::isKillService(receivedLmcpMessage->m_object)
                            //&& m_entityIdString.compare(std::static_pointer_cast<uxas::messages::uxnative::KillService>(receivedLmcpMessage->m_object)->getEntityID()) == 0//TODO check entityID
                            && m_networkIdString.compare(std::to_string(std::static_pointer_cast<uxas::messages::uxnative::KillService>(receivedLmcpMessage->m_object)->getServiceID())) == 0)
                            || processReceivedLmcpMessage(std::move(receivedLmcpMessage)))
                    {
                        UXAS_LOG_INFORM(m_networkClientTypeName, "::executeNetworkClient starting termination since received [", uxas::messages::uxnative::KillService::TypeName, "] message ");
                        m_isTerminateNetworkClient = true;
                    }
                }
            }
            catch (std::exception& ex)
            {
                UXAS_LOG_ERROR(m_networkClientTypeName, "::executeNetworkClient continuing infinite while loop after EXCEPTION: ", ex.what());
            }
        }
        
        // ZSRM debug
        std::cout << "Finished tid(" << gettid() << ")\n";
        
        UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::executeNetworkClient method END infinite while loop");

        m_isBaseClassTerminationFinished = true;

        uint32_t subclassTerminateDuration_ms{0};
        while (true)
        {
            m_isSubclassTerminationFinished = terminate();
            if (m_isSubclassTerminationFinished)
            {
                UXAS_LOG_INFORM(m_networkClientTypeName, "::executeNetworkClient terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
                break;
            }

            std::this_thread::sleep_for(std::chrono::milliseconds(m_subclassTerminationAttemptPeriod_ms));
            subclassTerminateDuration_ms += m_subclassTerminationAttemptPeriod_ms;
            if (subclassTerminateDuration_ms > m_subclassTerminationWarnDuration_ms)
            {
                UXAS_LOG_WARN(m_networkClientTypeName, "::executeNetworkClient has not terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
            }
            else if (subclassTerminateDuration_ms > m_subclassTerminationAbortDuration_ms)
            {
                UXAS_LOG_ERROR(m_networkClientTypeName, "::executeNetworkClient aborting termination of subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
                break;
            }
        }
        UXAS_LOG_INFORM(m_networkClientTypeName, "::executeNetworkClient exiting infinite loop thread [", std::this_thread::get_id(), "]");
        UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::executeNetworkClient method END");
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR(m_networkClientTypeName, "::executeNetworkClient EXCEPTION: ", ex.what());
    }
};

void
LmcpObjectNetworkClientBase::executeSerializedNetworkClient()
{
    try
    {
        UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::executeSerializedNetworkClient method START");
        UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::executeSerializedNetworkClient method START infinite while loop");
        m_isThreadStarted = true;
        while (!m_isTerminateNetworkClient)
        {
            // The first time we do not call wait for period but let the task wait for the first 
            // message, this way we "sync" the wait for next period with the message sender
            if (zs_isReservationEnabled && zs_isReserveAttached){
                zsv_wait_period(zs_schedfd,zs_rid);
            }

            // get the next serialized LMCP object message (if any) from the LMCP network server
            std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
                    nextReceivedSerializedLmcpObject
                    = m_lmcpObjectMessageReceiverPipe.getNextSerializedMessage();
            
            if (zs_isReservationEnabled && !zs_isReserveAttached){
                // attach it for the first time
                if (zsv_attach_reserve(zs_schedfd, gettid(), zs_rid)<0){
                    std::cout << "Error attaching the reserve \n";
                }
                zs_isReserveAttached = true;
            }

            if (nextReceivedSerializedLmcpObject)
            {
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING(m_networkClientTypeName, "::executeSerializedNetworkClient processing received LMCP message");
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING("Address:          [", nextReceivedSerializedLmcpObject->getAddress(), "]");
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING("ContentType:      [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getContentType(), "]");
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING("Descriptor:       [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getDescriptor(), "]");
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING("SourceGroup:      [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getSourceGroup(), "]");
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING("SourceEntityId:   [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getSourceEntityId(), "]");
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING("SourceServiceId:  [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getSourceServiceId(), "]");
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING("AttributesString: [", nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getString(), "]");
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING("getPayload:       [", nextReceivedSerializedLmcpObject->getPayload(), "]");
                UXAS_LOG_DEBUG_VERBOSE_MESSAGING("getString:        [", nextReceivedSerializedLmcpObject->getString(), "]");

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
                        UXAS_LOG_INFORM(m_networkClientTypeName, "::executeSerializedNetworkClient starting termination since received [", uxas::messages::uxnative::KillService::TypeName, "] message ");
                        m_isTerminateNetworkClient = true;
                    }
                }
                else if (processReceivedSerializedLmcpMessage(std::move(nextReceivedSerializedLmcpObject)))
                {
                    m_isTerminateNetworkClient = true;
                }
            }
        }

        UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::executeSerializedNetworkClient method END infinite while loop");
        
        m_isBaseClassTerminationFinished = true;

        uint32_t subclassTerminateDuration_ms{0};
        while (true)
        {
            m_isSubclassTerminationFinished = terminate();
            if (m_isSubclassTerminationFinished)
            {
                UXAS_LOG_INFORM(m_networkClientTypeName, "::executeSerializedNetworkClient terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
                break;
            }
            
            std::this_thread::sleep_for(std::chrono::milliseconds(m_subclassTerminationAttemptPeriod_ms));
            subclassTerminateDuration_ms += m_subclassTerminationAttemptPeriod_ms;
            if (subclassTerminateDuration_ms > m_subclassTerminationWarnDuration_ms)
            {
                UXAS_LOG_WARN(m_networkClientTypeName, "::executeSerializedNetworkClient has not terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
            }
            else if (subclassTerminateDuration_ms > m_subclassTerminationAbortDuration_ms)
            {
                UXAS_LOG_ERROR(m_networkClientTypeName, "::executeSerializedNetworkClient aborting termination of subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
                m_isSubclassTerminationFinished = true;
                break;
            }
        }
        UXAS_LOG_INFORM(m_networkClientTypeName, "::executeSerializedNetworkClient exiting infinite loop thread [", std::this_thread::get_id(), "]");
        UXAS_LOG_DEBUGGING(m_networkClientTypeName, "::executeSerializedNetworkClient method END");
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR(m_networkClientTypeName, "::executeSerializedNetworkClient EXCEPTION: ", ex.what());
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
        UXAS_LOG_ERROR("LmcpObjectMessageReceiverPipe::deserializeMessage failed to convert message payload string into an LMCP object");
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

/**
 * ZSRM methods
 */
void
LmcpObjectNetworkClientBase::zs_budget_enforcement_handler(int rid)
{    
    std::cout << "zs_budget_enforcement_handler("<<rid<<")\n";
}

void LmcpObjectNetworkClientBase::zs_set_budget_reservation_parameters(
                                            long period_secs,
                                            long period_nsecs,
                                            long zero_slack_secs,
                                            long zero_slack_nsecs,
                                            long nominal_wcet_secs,
                                            long nominal_wcet_nsecs,
                                            long overload_wcet_secs,
                                            long overload_wcet_nsecs,
                                            int criticality)
{
    zs_period_secs = period_secs;
    zs_period_nsecs = period_nsecs;
    zs_zero_slack_secs = zero_slack_secs;
    zs_zero_slack_nsecs = zero_slack_nsecs;
    zs_nominal_wcet_secs = nominal_wcet_secs;
    zs_nominal_wcet_nsecs = nominal_wcet_nsecs;
    zs_overload_wcet_secs = overload_wcet_secs;
    zs_overload_wcet_nsecs = overload_wcet_nsecs;
    zs_criticality = criticality;
    zs_isReservationEnabled = true;   
}

void 
LmcpObjectNetworkClientBase::setRuntimeAssuranceOn()
{
    rtaActive = true;
}
void 
LmcpObjectNetworkClientBase::setRuntimeAssuranceOff()
{
    rtaActive = false;
}

bool 
LmcpObjectNetworkClientBase::isRuntimeAssuranceOn()
{
    return rtaActive;
}
}; //namespace communications
}; //namespace uxas


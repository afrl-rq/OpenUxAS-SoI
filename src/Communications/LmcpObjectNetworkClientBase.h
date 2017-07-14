// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_NETWORK_CLIENT_BASE_H
#define UXAS_MESSAGE_LMCP_OBJECT_NETWORK_CLIENT_BASE_H

#include "LmcpObjectMessageReceiverPipe.h"
#include "LmcpObjectMessageSenderPipe.h"

#include "avtas/lmcp/Factory.h"

#include "pugixml.hpp"

#include <atomic>
#include <cstdint>
#include <memory>
#include <set>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

namespace uxas
{
namespace communications
{
/** \class LmcpObjectNetworkClientBase
 * 
 * \par Overview:     
 * The <B><i>LmcpObjectNetworkClientBase</i></B> is the base class for all classes 
 * that communicate across an <b>LMCP</b> network.  It has the following behaviors and characteristics: 
 * <ul style="padding-left:1em;margin-left:0">
 * <li>Configuration
 * <li>Initialization and Startup
 * <li>Threading
 * <li>Receiving <b>LMCP</b> object messages
 * <li>Sending <b>LMCP</b> object messages
 * <li>Termination
 * </ul>
 * 
 * \par Behaviors and Characteristics:
 * <ul style="padding-left:1em;margin-left:0">
 * <li><i>\u{Configuration}</i> first executes logic specific to configuration of this class, then calls 
 * the <B><i>configure</i></B> virtual method. Adding message subscription addresses 
 * is an example of logic that might be present in the <B><i>configure</i></B> method 
 * of an inheriting class.
 * 
 * <li><i>\u{Initialization and Startup}</i> consists of the following logical sequence 
 * (1) initialize this class; 
 * (2) initialize the inheriting class by calling the <B><i>initialize</i></B> virtual method; 
 * (3) start the inheriting class by calling the <B><i>start</i></B> virtual method; 
 * (4) start this class.
 * 
 * <li><i>\u{Threading}</i> consists of a single thread within this class and zero-many 
 * threads in an inheriting class. Inheriting classes that have their own threads 
 * must implement the <B><i>terminate</i></B> virtual method to achieve clean destruction.
 * 
 * <li><i>\u{Receiving <b>LMCP</b> object messages}</i> are processed by calling either the 
 * <B><i>processReceivedLmcpMessage</i></B> virtual method or the 
 * <B><i>processReceivedSerializedLmcpMessage</i></B> virtual method (as determined 
 * by configuration). Receiving any <b>LMCP</b> object message requires the appropriate 
 * configuration of message addresses. 
 * Uni-cast, multi-cast and broadcast messages are supported.
 * 
 * <li><i>\u{Sending <b>LMCP</b> object messages}</i> can be performed by inheriting classes 
 * by calling one of three methods: 
 * <B><i>sendLmcpObjectBroadcastMessage</i></B>, 
 * <B><i>sendLmcpObjectLimitedCastMessage</i></B> or 
 * <B><i>sendSerializedLmcpObjectMessage</i></B>. Uni-cast, multi-cast and broadcast 
 * messages are supported.
 * 
 * <li><i>\u{Termination}</i> can occur in two different ways. If true is returned by either the 
 * <B><i>processReceivedLmcpMessage</i></B> virtual method or the 
 * <B><i>processReceivedSerializedLmcpMessage</i></B> virtual method, then termination 
 * logic is executed. Alternatively, receiving the the appropriate <b>LMCP</b> object 
 * termination message results in termination. During termination, 
 * <B><i>terminate</i></B> virtual method is called that to execute logic that is 
 * specific to the inheriting class (e.g., thread joining).
 * </ul>
 * 
 * 
 * @n
 */

class LmcpObjectNetworkClientBase
{
public:

    /** \class ReceiveProcessingType
     * 
     * \par Enumeration specifying whether or not to de-serialize a received message.
     * 
     * \n
     */
    enum class ReceiveProcessingType
    {
        /** \brief Received <b>LMCP</b> objects are de-serialized */
        LMCP,
        /** \brief Received <b>LMCP</b> objects are not de-serialized */
        SERIALIZED_LMCP
    };
    
    /**
     * s_entityIdPrefix string (leading characters for indicating that an entity ID follows)
     * @return 
     */
    static std::string&
    s_entityIdPrefix() { static std::string s_string("eid"); return (s_string); };
    
    /**
     * s_serviceIdPrefix string (leading characters for indicating that a service ID follows)
     * @return 
     */
    static std::string&
    s_serviceIdPrefix() { static std::string s_string(".sid"); return (s_string); };

    /**
     * s_serviceIdAllSuffix string (trailing characters that are appended to entity cast address
     * to form cast-to-all services of a specific entity)
     * @return 
     */
    static std::string&
    s_serviceIdAllSuffix() { static std::string s_string(".sidall"); return (s_string); };

    /** \brief Multi-cast entity-based subscription address string 
     * 
     * @param entityId UxAS entity ID.
     * @return address string to used to send a message to all services hosted by  
     * a particular UxAS entity.
     */
    static std::string
    getEntityCastAddress(const uint32_t entityId)
    {
        return (s_entityIdPrefix() + std::to_string(entityId));
    };

    /** \brief Multi-cast subscription address string that addresses a message 
     * to all services of a specific entity.
     * 
     * @param entityId UxAS entity ID.
     * @return address string to used to send a message to all services hosted by  
     * a particular UxAS entity.
     */
    static std::string
    getEntityServicesCastAllAddress(const uint32_t entityId)
    {
        return (getEntityCastAddress(entityId) + s_serviceIdAllSuffix());
    };

    /** \brief Uni-cast service-based subscription address string 
     * 
     * @param entityId UxAS entity ID.
     * @param networkClientId UxAS bridge or service ID.
     * @return address string to used to send a message to a specific service 
     * hosted by a particular UxAS entity.
     */
    static std::string
    getNetworkClientUnicastAddress(const uint32_t entityId, const int64_t networkClientId)
    {
        return (getEntityCastAddress(entityId) + s_serviceIdPrefix() + std::to_string(networkClientId));
    };
    
    /** \brief Multi-cast entity-based subscription address string 
     * 
     * @param entityId UxAS entity ID.
     * @return address string to used to send a message to all services hosted by  
     * a particular UxAS entity.
     */
    static std::string
    getEntityCastAddress(const std::string entityId)
    {
        return (s_entityIdPrefix() + entityId);
    };

    /** \brief Uni-cast service-based subscription address string 
     * 
     * @param entityId UxAS entity ID.
     * @param networkClientId UxAS bridge or service ID.
     * @return address string to used to send a message to a specific service 
     * hosted by a particular UxAS entity.
     */
    static std::string
    getNetworkClientUnicastAddress(const uint32_t entityId, const std::string networkClientId)
    {
        return (getEntityCastAddress(entityId) + s_serviceIdPrefix() + networkClientId);
    };

    /** \brief Uni-cast service-based subscription address string 
     * 
     * @param entityId UxAS entity ID.
     * @param networkClientId UxAS bridge or service ID.
     * @return address string to used to send a message to a specific service 
     * hosted by a particular UxAS entity.
     */
    static std::string
    getNetworkClientUnicastAddress(const std::string& entityId, const std::string& networkClientId)
    {
        return (getEntityCastAddress(entityId) + s_serviceIdPrefix() + networkClientId);
    };

    static std::string
    getNetworkClientUnicastAddress(const std::string& entityId, const int64_t& networkClientId)
    {
        return (getEntityCastAddress(entityId) + s_serviceIdPrefix() + std::to_string(networkClientId));
    };

    static int64_t
    getUniqueEntitySendMessageId()
    {
        return (s_uniqueEntitySendMessageId++);
    };

    /**
     * \brief The <B><i>getUniqueNetworkClientId</i></B> returns a unique service ID. 
     * It returns the ID from a call to getUniqueNetworkClientId(), which are used as service IDs
     * 
     * @return unique service ID.
     */
    static int64_t
    getUniqueNetworkClientId()
    {
        s_nextNetworkClientId++;
        return (s_nextNetworkClientId);
    };
    
protected:

    /** \brief static ID of network clients, used to create unique IDs.  */
    static uint32_t s_nextNetworkClientId;
    
    /** \brief static entity service cast address.  */
    static std::string s_entityServicesCastAllAddress;
            
private:

    /** \brief static unique IDs.  */
    static int64_t s_uniqueEntitySendMessageId;
            
public:

    /** \brief Type name for the <B><i>LmcpObjectNetworkClientBase</i></B> class */
    static const std::string&
    s_typeName() { static std::string s_string("LmcpObjectNetworkClientBase"); return (s_string); };

    LmcpObjectNetworkClientBase();

    virtual
    ~LmcpObjectNetworkClientBase();

private:

    /** \brief Copy construction not permitted */
    LmcpObjectNetworkClientBase(LmcpObjectNetworkClientBase const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectNetworkClientBase const&) = delete;

public:

    // TODO consider LmcpObjectNetworkBridgeManager friend declaration and 
    // make configureNetworkClient protected
    /** \brief The <B><i>configureNetworkClient</i></B> method must be invoked 
     * before calling the <B><i>initializeAndStart</i></B> 
     * method.  It performs <B><i>LmcpObjectNetworkClientBase</i></B>-specific configuration 
     * and invokes the <B><i>configure</i></B> virtual method. 
     * 
     * @param subclassTypeName type name of the inheriting class.
     * @param receiveProcessingType enumeration determining whether or not received <b>LMCP</b> message will be de-serialized.
     * @param networkXmlNode XML node containing object configurations.
     * @return true if configuration succeeds; false if configuration fails.
     */
    bool
    configureNetworkClient(const std::string& subclassTypeName, ReceiveProcessingType receiveProcessingType, const pugi::xml_node& networkClientXmlNode);

    /** \brief The <B><i>initializeAndStart</i></B> must be invoked 
     * after calling the protected <B><i>configureNetworkClient</i></B> method.  
     * It performs the following steps:
     * <ul style="padding-left:1em;margin-left:0">
     * <li><B><i>LmcpObjectNetworkClientBase</i></B>-specific initialization
     * <li>inheriting class initialization (calls <B><i>initialize</i></B> virtual method)
     * <li>inheriting class startup (calls <B><i>start</i></B> virtual method)
     * <li><B><i>LmcpObjectNetworkClientBase</i></B>-specific startup
     * </ul>
     * 
     * @return true if all initialization and startup succeeds; false if initialization or startup fails.
     */
    bool
    initializeAndStart();

    bool
    getIsTerminationFinished() { return(m_isBaseClassTerminationFinished && m_isSubclassTerminationFinished); }

protected:

    /** \brief The virtual <B><i>configure</i></B> method is invoked by the 
     * <B><i>LmcpObjectNetworkClientBase</i></B> class after completing its own 
     * configuration. 
     * 
     * @param xmlNode XML node containing object configurations.
     * @return true if configuration succeeds; false if configuration fails.
     */
    virtual
    bool
    configure(const pugi::xml_node& xmlNode) { return (true); };

    /** \brief The virtual <B><i>initialize</i></B> method is invoked by the 
     * <B><i>LmcpObjectNetworkClientBase</i></B> class after completing 
     * configurations and before startup. 
     * 
     * @return true if initialization succeeds; false if initialization fails.
     */
    virtual
    bool
    initialize() { return (true); };

    /** \brief The virtual <B><i>start</i></B> method is invoked by the 
     * <B><i>LmcpObjectNetworkClientBase</i></B> class after initialization and
     * before starting its own thread. 
     * 
     * @return true if start succeeds; false if start fails.
     */
    virtual
    bool
    start() { return (true); };

    /** \brief The virtual <B><i>terminate</i></B> method can be implemented by 
     * inheriting classes to perform inheriting class termination logic 
     * (e.g., thread joining). 
     */
    virtual
    bool
    terminate() { return (true); };

    /** \brief The virtual <B><i>processReceivedLmcpMessage</i></B> is 
     * repeatedly invoked by the <B><i>LmcpObjectNetworkClientBase</i></B> class in an 
     * infinite loop until termination. 
     * 
     * @param receivedLmcpObject received <b>LMCP</b> object.
     * @return true if object is to terminate; false if object is to continue processing.
     */
    virtual
    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) { return (false); };
    
    /** \brief The virtual <B><i>processReceivedSerializedLmcpMessage</i></B> is 
     * repeatedly invoked by the <B><i>LmcpObjectNetworkClientBase</i></B> class in an 
     * infinite loop until termination. The payload of the <B><i>AddressedAttributedMessage</i></B> 
     * is a serialized <b>LMCP</b> object. 
     * 
     * @param receivedSerializedLmcpObject received AddressedAttributedMessage object with serialized <b>LMCP</b> object payload.
     * @return true if object is to terminate; false if object is to continue processing.
     */
    virtual
    bool
    processReceivedSerializedLmcpMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> receivedSerializedLmcpMessage) { return (false); };
    
public:
    /** \brief The <B><i>addSubscriptionAddress</i></B> can be invoked 
     * at any time to add specified message subscription address. 
     * 
     * @param address message subscription value
     * @return true if address is added; false if address is not added.
     */
    bool
    addSubscriptionAddress(const std::string& address);

    /** \brief The <B><i>removeSubscriptionAddress</i></B> can be invoked 
     * at any time to remove specified message subscription address. 
     * 
     * @param address message subscription address
     * @return true if address is removed; false if address is not removed.
     */
    bool
    removeSubscriptionAddress(const std::string& address);    
    
    /** \brief The <B><i>removeAllSubscriptionAddresses</i></B> can be invoked 
     * at any time to remove message subscription addresses. 
     * 
     * @param address message subscription address
     * @return true if address is removed; false if address is not removed.
     */
    bool
    removeAllSubscriptionAddresses();

    
    /** \brief The <B><i>sendSharedLmcpObjectBroadcastMessage</i></B> method can be 
     * invoked to broadcast a <b>LMCP</b> object message on the <b>LMCP</b> network.
     *
     * <b>Temporarily made public to support Rust interop</b>
     * 
     * @param lmcpObject <b>LMCP</b> object to be broadcasted. The message publish 
     * address is derived from the full <b>LMCP</b> object name.
     */
    void
    sendSharedLmcpObjectBroadcastMessage(const std::shared_ptr<avtas::lmcp::Object>& lmcpObject);
    
protected:
    /** \brief The <B><i>sendLmcpObjectBroadcastMessage</i></B> method can be 
     * invoked to broadcast a <b>LMCP</b> object message on the <b>LMCP</b> network. 
     * 
     * @param lmcpObject <b>LMCP</b> object to be broadcasted. The message publish 
     * address is derived from the full <b>LMCP</b> object name.
     */
    void
    sendLmcpObjectBroadcastMessage(std::unique_ptr<avtas::lmcp::Object> lmcpObject);

    /** \brief The <B><i>sendLmcpObjectLimitedCastMessage</i></B> method can be 
     * invoked to send a uni-cast or multi-cast <b>LMCP</b> object message to the <b>LMCP</b> network. 
     * 
     * @param castAddress message publish address
     * @param lmcpObject <b>LMCP</b> object to be uni-casted/multi-casted.
     */
    void
    sendLmcpObjectLimitedCastMessage(const std::string& castAddress, std::unique_ptr<avtas::lmcp::Object> lmcpObject);

    /** \brief The <B><i>sendSerializedLmcpObjectMessage</i></B> method can be 
     * invoked to send a <B><i>AddressedAttributedMessage</i></B> to the <b>LMCP</b> network. The 
     * <B><i>AddressedAttributedMessage</i></B> payload must be a serialized <b>LMCP</b> object string. 
     * 
     * @param serializedLmcpObject <b>LMCP</b> object to be sent (uni-cast/multi-cast/broadcast).
     */
    void
    sendSerializedLmcpObjectMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> serializedLmcpObject);

    /** \brief The <B><i>sendSharedLmcpObjectLimitedCastMessage</i></B> method can be 
     * invoked to send a uni-cast or multi-cast <b>LMCP</b> object message to the <b>LMCP</b> network. 
     * 
     * @param castAddress message publish address
     * @param lmcpObject <b>LMCP</b> object to be uni-casted/multi-casted.
     */
    void
    sendSharedLmcpObjectLimitedCastMessage(const std::string& castAddress, const std::shared_ptr<avtas::lmcp::Object>& lmcpObject);

private:
    
    /** \brief The <B><i>initializeNetworkClient</i></B> method is invoked by 
     * the <B><i>initializeAndStart</i></B> method to perform 
     * <B><i>LmcpObjectNetworkClientBase</i></B>-specific initialization 
     * 
     * @return true if initialization succeeds; false if initialization fails.
     */
    bool
    initializeNetworkClient();

    /** \brief If <B><i>m_receiveProcessingType</i></B> == 
     * <B><i>ReceiveProcessingType::LMCP</i></B>, then 
     * the <B><i>executeNetworkClient</i></B> method repeatedly invokes 
     * the <B><i>processReceivedLmcpMessage</i></B> in an infinite loop until 
     * termination. Otherwise, the <B><i>executeNetworkClient</i></B> method is 
     * not invoked.
     */
    void
    executeNetworkClient();

    /** \brief If <B><i>m_receiveProcessingType</i></B> == 
     * <B><i>ReceiveProcessingType::SERIALIZED_LMCP</i></B>, then 
     * the <B><i>executeSerializedNetworkClient</i></B> method repeatedly invokes 
     * the <B><i>processReceivedSerializedLmcpMessage</i></B> in an infinite loop until 
     * termination. Otherwise, the <B><i>executeSerializedNetworkClient</i></B> method is 
     * not invoked.
     */
    void
    executeSerializedNetworkClient();

    /** \brief The <B><i>deserializeMessage</i></B> method deserializes an LMCP 
     * string into an LMCP object.
     * 
     * @return unique pointer to LMCP object if succeeds; unique pointer with 
     * unassigned native pointer. 
     */
    std::shared_ptr<avtas::lmcp::Object>
    deserializeMessage(const std::string& payload);
    
public:
    
    /** \brief Unique ID for UxAS entity instance; value read from configuration XML */
    uint32_t m_entityId;

    /** \brief String representation of the unique ID for UxAS entity instance; value read from configuration XML */
    std::string m_entityIdString;

    /** \brief Unique ID of the <b>LMCP</b> object communication network actor (e.g., bridge or service).  */
    int64_t m_networkId;

    /** \brief String representation of the unique ID of the <b>LMCP</b> object communication network actor (e.g., bridge or service).  */
    std::string m_networkIdString;

    /** \brief Unicast message address for messaging case of sending message to only this network client instance */
    std::string m_entityIdNetworkIdUnicastString;

    /** \brief Name of subclass used for logging/messaging.  */
    std::string m_networkClientTypeName;

protected:
    
    /** \brief Multi-cast group address that is subscribed to and included in sent messages  */
    std::string m_messageSourceGroup;

    /** \brief Type of UxAS entity instance; value read from configuration XML*/
    std::string m_entityType;

    std::atomic<bool> m_isBaseClassKillServiceProcessingPermitted{true};
    std::atomic<bool> m_isTerminateNetworkClient{false};
    std::atomic<bool> m_isBaseClassTerminationFinished{false};
    std::atomic<bool> m_isSubclassTerminationFinished{false};
    
    uint32_t m_subclassTerminationAbortDuration_ms{10000};
    uint32_t m_subclassTerminationWarnDuration_ms{3000};
    uint32_t m_subclassTerminationAttemptPeriod_ms{500};

private:
    
    /** \brief  */
    bool m_isConfigured{false};

    /** \brief  */
    bool m_isThreadStarted{false};

    /** \brief  this is the unique ID for the entity represented by this instance of the UxAS software, configured in component manager XML*/
    ReceiveProcessingType m_receiveProcessingType;

    /** \brief Pointer to the component's thread.  */
    std::unique_ptr<std::thread> m_networkClientThread;

    uxas::communications::LmcpObjectMessageReceiverPipe m_lmcpObjectMessageReceiverPipe;
    std::set<std::string> m_preStartLmcpSubscriptionAddresses;

    uxas::communications::LmcpObjectMessageSenderPipe m_lmcpObjectMessageSenderPipe;
    
};

}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_LMCP_OBJECT_NETWORK_CLIENT_BASE_H */

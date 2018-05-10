// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_NETWORK_ZEROMQ_SUBSCRIBE_PUSH_BRIDGE_H
#define UXAS_MESSAGE_LMCP_OBJECT_NETWORK_ZEROMQ_SUBSCRIBE_PUSH_BRIDGE_H

#include "LmcpObjectMessageReceiverPipe.h"
#include "LmcpObjectMessageSenderPipe.h"
#include "LmcpObjectNetworkClientBase.h"

#include <atomic>
#include <cstdint>

namespace uxas
{
namespace communications
{

/** \class LmcpObjectNetworkSubscribePushBridge
 *  \brief A service that connects an external entity to the internal message
 * bus using <I>ZMQ_SUB<I/> and <I>ZMQ_PUSH<I/> sockets.
 * 
 * @par Example:
 * <Bridge Type="LmcpObjectNetworkSubscribePushBridge"
 *    AddressSUB="tcp://localhost:5555"
 *    AddressPUSH="tcp://localhost:5556"
 *    ConsiderSelfGenerated="false">
 *
 * AddressSUB: the address and port for the ZeroMQ subscription connection
 * AddressPUSH: the address and port for the ZeroMQ push connection
 * ConsiderSelfGenerated: boolean that when true sends local messages with bridge service ID
 * 
 *  @par Description:
 * The <B>Subscribe/Push Bridge<B/> component connects to external entities using
 * <I>ZMQ_SUB<I/> and <I>ZMQ_PUSH<I/> sockets. The external entity sends messages to the 
 * <B>Subscribe/Push Bridge<B/> using a ZeroMQ PUB socket and receives messages using
 * a PULL socket. The the <B>Subscribe/Push Bridge<B/> sends messages received from
 * the external entity to the local @ref c_CommunicationHub. Subscribed messages
 * received from the local @ref c_CommunicationHub are sent to the external entity.
 * 
 * @par Details:
 * <ul style="padding-left:1em;margin-left:0">
 * <li> Message Subscription - 
 * The subscriptions for messages from the local @ref c_CommunicationHub to be
 * sent to the external entity are set in the configuration file, e.g.:
 * 
 * <I>"<SubscribeToLocalMessage MessageType=""lmcp:""/>"<I/>
 * 
 * The subscriptions for messages to be sent from the external entity's ZMQ_PUB
 * socket and sent to the local @ref c_CommunicationHub are set in the configuration
 * file, e.g.:
 * 
 * <I>"<SubscribeToExternalMessage MessageType=""lmcp:""/>"<I/>
 * 
 * 
 * <li> Addressing -
 * The TCP/IP addresses for the SUB and PUSH sockets are set via the configuration
 * file. The attribute: <B><I>AddressSUB<I/><B/> is used to set the address 
 * for the SUB socket, see @ref m_ptr_ZsckSubscribe. The attribute: <B><I>AddressPUSH<I/><B/>
 * is used to set the address of the PUSH socket, see @ref m_ptr_ZsckPush
 * 
 * </ul> @n
 * 
 */

class LmcpObjectNetworkSubscribePushBridge : public LmcpObjectNetworkClientBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("LmcpObjectNetworkSubscribePushBridge"); return (s_string); };

    LmcpObjectNetworkSubscribePushBridge();

    ~LmcpObjectNetworkSubscribePushBridge();

private:

    /** \brief Copy construction not permitted */
    LmcpObjectNetworkSubscribePushBridge(LmcpObjectNetworkSubscribePushBridge const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectNetworkSubscribePushBridge const&) = delete;

public:

    bool
    configure(const pugi::xml_node& bridgeXmlNode) override;

private:

    bool
    initialize() override;

    bool
    start() override;

    bool
    terminate() override;
    
    bool
    processReceivedSerializedLmcpMessage(
                                std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
                                receivedLmcpMessage) override;

    void
    executeExternalSerializedLmcpObjectReceiveProcessing();

    std::atomic<bool> m_isTerminate{false};

    /** \brief External receive processing thread.  */
    std::unique_ptr<std::thread> m_externalReceiveProcessingThread;

    /** \brief  This is ID that will prefix messages from other entities to this entity*/
    std::string m_remoteConfigurationString;

    uxas::communications::LmcpObjectMessageReceiverPipe m_externalLmcpObjectMessageReceiverPipe;
    std::set<std::string> m_externalSubscriptionAddresses;
    std::set<std::string> m_nonImportForwardAddresses;
    std::set<std::string> m_nonExportForwardAddresses;

    uxas::communications::LmcpObjectMessageSenderPipe m_externalLmcpObjectMessageSenderPipe;

    std::string m_externalSubscribeSocketAddress = std::string("tcp://*:5555");
    std::string m_externalPushSocketAddress = std::string("tcp://*:5556");
    bool m_isConsideredSelfGenerated{ false };
};

}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_LMCP_OBJECT_NETWORK_ZEROMQ_SUBSCRIBE_PUSH_BRIDGE_H */


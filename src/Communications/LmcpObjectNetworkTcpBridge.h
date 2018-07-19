// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_NETWORK_TCP_BRIDGE_H
#define UXAS_MESSAGE_LMCP_OBJECT_NETWORK_TCP_BRIDGE_H

#include "LmcpObjectNetworkClientBase.h"
#include "LmcpObjectMessageTcpReceiverSenderPipe.h"

#include <atomic>
#include <cstdint>
#include <functional>
#include <map>
#include <mutex>
#include <thread>
#include <set>

//MIGRATION source
//n_UxAS_Components::c_Component_TcpBridge
//commit 24340ad065352dc86a98e9d4d0a80738337e9a93
//Author: derek.kingston <derek.kingston@us.af.mil>
//Date:   Sat Aug 1 21:07:28 2015 -0400
//    Impact specific compile option plus with final waypoint fix

namespace uxas
{
namespace communications
{

/** \class LmcpObjectNetworkTcpBridge
    \brief A service that connects an external TCP/IP stream to the internal message bus.

 * 
 * 
 *  @par Description:
 * The <B>TCP Bridge<B/> component connects to external entities using a
 * ZeroMQ ZMQ_STREAM socket. The external entity sends and receives LMCP messages
 * to/from the UxAS in TCP streams. The <B>TCP Bridge<B/> receives subscribed
 * messages from the local bus, serializes them, and sends them to the external
 * entity. Messages from the external entity are converted to LMCP objects and
 * sent to the local bus
 * 
 * @par Details:
 * <ul style="padding-left:1em;margin-left:0">
 * <li> Message Subscription - 
 * The external entity subscribes to messages through the PUB socket using "setsockopt", e.g.:
 * 
 * <li> Subscription -
 * Subscribed messages are configured through a XML configuration string. The
 * <B><I>SubscribeToMessages<I/><B/> XML node contains <B><I>SubscribeToMessage<I/><B/>
 * XML nodes that contain the messages to subscribe.
 * 
 * <li> Client/Server -
 * The <B>TCP Bridge<B/> acts as a client, by default. If the configuration file
 * attribute: <B><I>Server<I/><B/> is set to "true", then the <B>TCP Bridge<B/>
 * acts as a server.
 * 
 * <li> Addressing -
 * The TCP/IP addresses for the ZMQ_STREAM socket is set via the configuration
 * file. The attribute: <B><I>TcpAddress<I/><B/> is used to set the address, 
 * see @ref m_ptr_ZsckTcpConnection.
 * 
 * 
 * 
 * </ul> @n
 * 
 * 
 * 
 * 
 */

class LmcpObjectNetworkTcpBridge : public LmcpObjectNetworkClientBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("LmcpObjectNetworkTcpBridge"); return (s_string); };

    LmcpObjectNetworkTcpBridge();

    ~LmcpObjectNetworkTcpBridge();

private:

    /** \brief Copy construction not permitted */
    LmcpObjectNetworkTcpBridge(LmcpObjectNetworkTcpBridge const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectNetworkTcpBridge const&) = delete;

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
    processReceivedSerializedLmcpMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
                                receivedLmcpMessage) override;

    void
    executeTcpReceiveProcessing();

    std::atomic<bool> m_isTerminate{false};

    /** \brief External TCP processing thread.  */
    std::unique_ptr<std::thread> m_tcpProcessingThread;

    std::string m_remoteConfigurationString;

    uxas::communications::LmcpObjectMessageTcpReceiverSenderPipe m_externalLmcpObjectMessageTcpReceiverSenderPipe;

    std::set<std::string> m_nonImportForwardAddresses;
    std::set<std::string> m_nonExportForwardAddresses;

    /// \brief  this is the tcp/ip address, including port, of the PUB
    /// socket, e.g.  "tcp://xxx.xxx.xxx.xxx:5555" or "tcp://*:5555". Used to
    /// relay messages to the external entity.
    std::string m_tcpReceiveSendAddress = std::string("tcp://*:5555");
    /** \brief  If this is set to true the TcpBridge connects (binds) as a server. 
     If it is false the TcpBridge connects as a client. Defaults to true */
    bool m_isServer{true};
    /** \brief  If this is set to `true`, the TcpBridge service will report all received
     * messages as if they originated from the vehicle hosting the TcpBridge rather
     * than the external sender. This can be used when connected directly to a vehicle 
     * simulation where the messages received would be considered self-generated in
     * normal operation. */
    bool m_isConsideredSelfGenerated{true};
    
    std::map<std::string, std::string> m_messageAddressToAlias;
};

}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_LMCP_OBJECT_NETWORK_TCP_BRIDGE_H */


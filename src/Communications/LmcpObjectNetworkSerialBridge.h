// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_NETWORK_SERIAL_BRIDGE_H
#define UXAS_MESSAGE_LMCP_OBJECT_NETWORK_SERIAL_BRIDGE_H

#include "LmcpObjectNetworkClientBase.h"

#include "UxAS_SentinelSerialBuffer.h"

#include "serial/serial.h"

#include <atomic>
#include <cstdint>

namespace uxas
{
namespace communications
{

/** \class LmcpObjectNetworkSerialBridge
    \brief A component that connects an external TCP/IP stream to the internal message bus.

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

class LmcpObjectNetworkSerialBridge : public LmcpObjectNetworkClientBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("LmcpObjectNetworkSerialBridge"); return (s_string); };
    
    LmcpObjectNetworkSerialBridge();

    ~LmcpObjectNetworkSerialBridge();

private:

    /** \brief Copy construction not permitted */
    LmcpObjectNetworkSerialBridge(LmcpObjectNetworkSerialBridge const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectNetworkSerialBridge const&) = delete;

private:

    bool
    configure(const pugi::xml_node& bridgeXmlNode) override;

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
    executeSerialReceiveProcessing();

    std::atomic<bool> m_isTerminate{false};

    /** \brief External TCP processing thread.  */
    std::unique_ptr<std::thread> m_serialProcessingThread;
    
    std::unique_ptr<serial::Serial> m_serialConnection;

    std::string m_serialPortAddress = std::string("/dev/ttyO2");

    /** \brief the baud rate of the serial port */
    uint32_t m_serialBaudRate{57600}; // (57600 bits/second)/8 = 7200 bytes/second; (9600 bits/second)/8 = 1200 bytes/second
    
    /** \brief serial connection read timeout
     * 
     * 20150819 DBK, RJT: latency up to 100ms (resulting from serial timeout value of 100ms) satisfies UxAS system requirements.
     */ 
    uint32_t m_serialTimeout_ms{100}; 

    /** \brief maximum number of characters to read from serial connection
     * 
     * 20150819 DBK, RJT: approximate maximum size of an object is expected to be 300-500 bytes.
     */
    uint32_t m_serialMaxBytesReadCount{1000};

    uxas::common::SentinelSerialBuffer m_receiveSerialDataBuffer;
    
    std::set<std::string> m_externalSubscriptionAddresses;
    std::set<std::string> m_nonImportForwardAddresses;
    std::set<std::string> m_nonExportForwardAddresses;
    
    /** \brief  If this is set to `true`, the TcpBridge service will report all received
     * messages as if they originated from the vehicle hosting the TcpBridge rather
     * than the external sender. This can be used when connected directly to a vehicle 
     * simulation where the messages received would be considered self-generated in
     * normal operation. */
    bool m_isConsideredSelfGenerated{true};

};

}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_LMCP_OBJECT_NETWORK_SERIAL_BRIDGE_H */


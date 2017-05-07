// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   TcpBridge.h
 * Author: steve
 *
 * Created on March 28, 2014, 3:03 PM
 */

#ifndef UXAS_TCP_BRIDGE_H
#define UXAS_TCP_BRIDGE_H

#include "ServiceBase.h"

#include "afrl/cmasi/AirVehicleState.h"

#include <deque>
#include <mutex>

namespace uxas
{
namespace service
{
namespace adapter
{

/*! \class TcpBridge
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
 * <BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR>
 * 
 * 
 */

class TcpBridge : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("TcpBridge");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };

    static const std::string&
    s_directoryName()
    {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create()
    {
        return new TcpBridge;
    };

    TcpBridge();

    virtual
    ~TcpBridge();

private:

    static
    ServiceBase::CreationRegistrar<TcpBridge> s_registrar;

    /** brief Copy construction not permitted */
    TcpBridge(TcpBridge const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(TcpBridge const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    bool
    start() override;

    bool
    terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


private:
    void ReceiveTcpMessages();
    /*! \brief This function attempts to produce an LMCP object from the given stream, 
     * partial streams are saved between calls to this function */
    bool bLmcpObjectFromStream(std::string& strMessageStream, std::shared_ptr<avtas::lmcp::Object>& ptr_Object, std::stringstream& sstrError);
    /*! \brief This function attempts to produce an LMCP object from the given string */
    static bool bLmcpObjectFromString(const std::string& strMessage, std::shared_ptr<avtas::lmcp::Object>& ptr_Object, std::stringstream& sstrError);

    std::atomic<bool> m_isTerminate{false};
    std::unique_ptr<std::thread> m_receiveTcpMessagesThread;

    /*! \brief this is the zmq context used to connect to the axis device */
    std::shared_ptr<zmq::context_t> m_ptr_zmqContextReceive;
    /*! \brief this is the stream socket used to connect to the axis device */
    std::shared_ptr<zmq::socket_t> m_ptr_ZsckTcpConnection;
    /*! \brief  this is the tcp/ip address, including port, of the PUB
     * socket, e.g.  "tcp://xxx.xxx.xxx.xxx:5555" or "tcp://*:5555". Used to
     * relay messages to the external entity. */
	std::string m_strTcpAddress = std::string("tcp://*:5555");
    /*! \brief  If this is set to true the the TcpBridge connects (binds) as a server. 
     If it is false the TcpBridge connects as a client. Defaults to false */
    bool m_bServer{false};
    /*! \brief  This is the ID (256 bytes) of the last connection that data was received from
     TODO:: CAN ONLY HANDLE ONE CONNECTION !!!!*/
    uint8_t m_id [256];
    size_t m_szSizeID{0};
    std::string m_strConnectionID;
    /*! \brief  buffer for partial strings while converting streams to lmcp messages*/
    std::string m_streamBuffer;

    /*! \brief  number of messages received*/
    uint32_t m_ui32MessageCount_Receive{0};
    /*! \brief  number of messages received*/
    uint32_t m_ui32MessageCount_Receive_0{0};

    std::deque<std::shared_ptr<avtas::lmcp::Object> > m_messagesToSend;
    
    /*! \brief  mutex to protect the TCP-IP socket */
    std::mutex m_mutex;

    void addMessageToSend(std::shared_ptr<avtas::lmcp::Object>& messageToSend)
    {
        std::unique_lock<std::mutex> lock(m_mutex);
        m_messagesToSend.push_front(messageToSend);
    }
    std::shared_ptr<avtas::lmcp::Object> getNextMessageToSend()
    {
        std::unique_lock<std::mutex> lock(m_mutex);
        std::shared_ptr<avtas::lmcp::Object> messageToSend;
        if(!m_messagesToSend.empty())
        {
            messageToSend = m_messagesToSend.back();
            m_messagesToSend.pop_back();
        }
        return(messageToSend);
    }
    
};

}; //namespace adapter
}; //namespace service
}; //namespace uxas

#endif /* UXAS_TCP_BRIDGE_H */


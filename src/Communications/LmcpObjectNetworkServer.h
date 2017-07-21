// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_NETWORK_SERVER_H
#define UXAS_MESSAGE_LMCP_OBJECT_NETWORK_SERVER_H

#include "AddressedAttributedMessage.h"
#include "LmcpObjectMessageReceiverPipe.h"
#include "LmcpObjectMessageSenderPipe.h"

#include <atomic>
#include <memory>
#include <thread>

namespace uxas
{
namespace communications
{

/** \class LmcpObjectNetworkServer
 * 
 * @par Description:     
 * The <B><i>LmcpObjectNetworkServer</i></B> is central message hub.
 * 
 * @par Highlights:
 * <ul style="padding-left:1em;margin-left:0">
 * <li> Self-Registration - 
 * The component class is self registering and can be instantiated using a 
 * string registered by the component. This makes it possible to add new 
 * component classes without modifying existing component manager functions.
 * 
 * <li> Configuration -
 * Configuration is accomplished by a call to the function bConfigure(...)
 * before component execution begins or by using a ZeroMQ SUB socket to
 * receive the requested XML configuration nodes after component execution has started.
 * 
 * <li> Thread Management -
 * The component executes in its own thread which is controlled using a
 * a ZeroMQ PUB-SUB connection to pass thread control messages to the 
 * component.
 * 
 * <li> LMCP messaging -
 * The component subscribes to desired messages from the CommunicationHub's
 * ZeroMQ PUB socket and sends messages to the hub using a ZeroMQ PUSH socket.
 * Each message a component publishes also includes sending service
 * ID and entity ID.
 * </ul>
 * 
 * 
 * @n
 */

class LmcpObjectNetworkServer final
{
        
public:

    LmcpObjectNetworkServer();

    ~LmcpObjectNetworkServer();

private:

    static const std::string&
    s_typeName() { static std::string s_string("LmcpObjectNetworkServer"); return (s_string); };

    /** \brief Copy construction not permitted */
    LmcpObjectNetworkServer(LmcpObjectNetworkServer const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectNetworkServer const&) = delete;

public:

    /** \brief The <B><i>configure</i></B> function must be invoked 
     * before calling the <B><i>initializeAndStart</i></B> function. */
    bool
    configure();
    
    /** \brief The <B><i>initializeAndStart</i></B> function must be invoked 
     * after calling the <B><i>configure</i></B> function. */
    bool
    initializeAndStart();

    /** \brief The <B><i>terminate</i></B> can be invoked 
     * after calling the <B><i>initializeAndStartNetworkClientBaseAndDerived</i></B> 
     * function to discontinue receiving and processing network messages. */
    void
    terminate();

private:
    
    /** \brief The <B><i>initialize</i></B> function must be invoked 
     * before calling the <B><i>initializeAndStartNetworkClientBaseAndDerived</i></B> 
     * function.  It performs LmcpObjectNetworkServer specific configuration. */
    bool
    initialize();

    void
    executeNetworkServer();
    
    /** \brief  this is the unique ID for the entity represented by this instance of the UxAS software, configured in component manager XML*/
    uint32_t m_entityId;

    /** \brief unique ID of the component.  */
    uint32_t m_networkId{1};

    /** \brief Pointer to the component's thread.  */
    std::unique_ptr<std::thread> m_thread;

protected:

    uxas::communications::LmcpObjectMessageReceiverPipe m_lmcpObjectMessageReceiverPipe;

    uxas::communications::LmcpObjectMessageSenderPipe m_lmcpObjectMessageSenderPipe;
    
private:

    std::atomic<bool> m_isTerminate{false};

};

}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_LMCP_OBJECT_NETWORK_SERVER_H */

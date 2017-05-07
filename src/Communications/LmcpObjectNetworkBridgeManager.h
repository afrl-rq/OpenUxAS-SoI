// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_NETWORK_BRIDGE_MANAGER_H
#define UXAS_MESSAGE_LMCP_OBJECT_NETWORK_BRIDGE_MANAGER_H

#include "LmcpObjectNetworkClientBase.h"

#include "LmcpObjectMessageReceiverPipe.h"

#include <memory>
#include <thread>
#include <unordered_map>
#include <vector>

namespace uxas
{
namespace communications
{

/** \class LmcpObjectNetworkBridgeManager
 * 
 * \brief Manage services; can support dynamic service addition and termination 
 * based on LMCP object messages received local or remote service.
 * 
 * @par Description:
 * The <B><i>LmcpObjectNetworkBridgeManager</i></B> manages the creation, initialization, 
 * configuration, launch and termination of UxAS services.  
 * It is started during UxAS entity initialization and runs for the full 
 * duration of the life of the UxAS entity.  It runs on a dedicated thread 
 * and is started using the @ref StartComponentManager function.
 * 
 * The <I>Bridge Manager</I> is designed to
 * execute, for the life of the UxAS program, it its own thread. It is 
 * initiated through a call to the function @ref StartComponentManager. This
 * creates a thread and calls @ref LmcpObjectNetworkBridgeManagerExecutitve to start the 
 * executive. The executive function loads the 
 * @ref ProcessXmlConfigurationFile, and enters the main loop.
 * 
 * @par Usage:
 * <ul style="padding-left:1em;margin-left:0">
 * <li>Instantiate (invoke constructor)
 * <li>Configure (invoke configureBridge method)
 * <li>Initialize and start (invoke initializeAndStartBridge method)
 * </ul>
 * 
 * @par Highlights:
 * <ul style="padding-left:1em;margin-left:0">
 * <li> Communication - 
 * The <I>Bridge Manager</I> utilizes ZeroMQ sockets for controlling
 * threads and, sending and receiving LMCP messages:
 * 
 * <B>ZMQ_PUB</B> is used to send thread control messages to services, 
 * @ref n_UxAS_Constants::c_Constants_Control::strGetInProc_ThreadControl()
 * 
 * <B>ZMQ_SUB</B> is used to receive thread control messages from  services, 
 * @ref n_UxAS_Constants::c_Constants_Control::strGetInProc_ManagerThreadControl()
 * 
 * <B>ZMQ_SUB</B> is used to receive LMCP messages from the <I>Message Hub</I>, 
 * @ref n_UxAS_Constants::c_Constants_Control::strGetInProc_FromMessageHub()
 * 
 * <B>ZMQ_PUSH</B> is used to send LMCP messages to the <I>Message Hub</I>, 
 * @ref n_UxAS_Constants::c_Constants_Control::strGetInProc_ToMessageHub()
 *
 * 
 * <li> Bridge Creation/Configuration -
 * Components are created/configured either as a result of entries in the 
 * configuration file, @ref ProcessXmlConfigurationFile, or as a response to
 * LMCP "task" messages(TODO::adding tasks based on message is not 
 * implemented yet). When a service is created a starting ID is passed in 
 * that represents the start of the range of message IDs to be used by the 
 * service.
 * 
 * Pointers to services are stored, by ID, in the unordered map: 
 * @ref m_um_sz_ptr_compComponents. 
 * 
 * <li> Bridge Termination -
 * Components are terminated as a result of <I>KillAll</I> or 
 * <I>KillComponent</I> messages from the program's <I>ThreadControl</I>, 
 * @ref n_UxAS_Constants::c_Constants_Control::strGetMsg_KillAll(),
 * @ref n_UxAS_Constants::c_Constants_Control::strGetMsg_KillComponent(),
 * @ref n_UxAS_Constants::c_Constants_Control::strGetInProc_ThreadControl().
 * 
 * Components are also terminated based on <B>"CMASI::RemoveTasks"</B> messages.
 * 
 * </ul> @n
 */

class LmcpObjectNetworkBridgeManager final
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("LmcpObjectNetworkBridgeManager"); return (s_string); };

    static LmcpObjectNetworkBridgeManager&
    getInstance();

    ~LmcpObjectNetworkBridgeManager() { };

private:

    /** \brief Public, direct construction not permitted (singleton pattern) */
    LmcpObjectNetworkBridgeManager() { };

    /** \brief Copy construction not permitted */
    LmcpObjectNetworkBridgeManager(LmcpObjectNetworkBridgeManager const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectNetworkBridgeManager const&) = delete;

    static std::unique_ptr<LmcpObjectNetworkBridgeManager> s_instance;

public:

    bool
    initialize();
    
    std::unordered_map<uint32_t, std::unique_ptr<LmcpObjectNetworkClientBase>>
    createTestBridges(const std::string& cfgXmlFilePath, uint32_t entityId, uint32_t firstNetworkId);
    
private:
    
    std::unique_ptr<LmcpObjectNetworkClientBase>
    createBridge(const pugi::xml_node& bridgeXmlNode, uint32_t entityId, uint32_t networkId);

    bool m_isInitializedBridges{false};
    std::unordered_map<uint32_t, std::unique_ptr<LmcpObjectNetworkClientBase>> m_bridgesByNetworkId;

};

}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_LMCP_OBJECT_NETWORK_BRIDGE_MANAGER_H */

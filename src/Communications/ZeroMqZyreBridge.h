// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_ZERO_MQ_ZYRE_BRIDGE_H
#define UXAS_MESSAGE_ZERO_MQ_ZYRE_BRIDGE_H

#include "UxAS_Zyre.h"

#include <atomic>
#include <functional>
#include <memory>
#include <mutex>
#include <set>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

namespace uxas
{
namespace communications
{

/** \class ZeroMqZyreBridge
 *  \brief A service that provides network discovery and communications.
 * Dynamically discovers and bridges with zero-many Zyre-enabled systems.
 */
class ZeroMqZyreBridge
{

public:

    static const std::string&
    s_typeName() { static std::string s_string("ZeroMqZyreBridge"); return (s_string); };
   
    ZeroMqZyreBridge();
    
    virtual ~ZeroMqZyreBridge();

private:

    /** \brief Copy construction not permitted */
    ZeroMqZyreBridge(ZeroMqZyreBridge const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(ZeroMqZyreBridge const&) = delete;

public:

    void
    setZyreEnterMessageHandler(std::function<void(const std::string& zyreRemoteUuid, const std::unordered_map<std::string, std::string>& headerKeyValuePairs)>&& zyreEnterMessageHandler);

    void
    setZyreExitMessageHandler(std::function<void(const std::string& zyreRemoteUuid)>&& zyreExitMessageHandler);

    void
    setZyreWhisperMessageHandler(std::function<void(const std::string& zyreRemoteUuid, const std::string& messagePayload)>&& zyreWhisperMessageHandler);

    /**
     * Starts (or re-starts) Zyre node
     * @param zyreNetworkDevice
     * @param zyreEndpoint
     * @param gossipEndpoint
     * @param isGossipBind
     * @param zyreNodeId
     * @param headerKeyValuePairs
     * @return 
     */
    bool
    start(const std::string& zyreNetworkDevice, const std::string& zyreEndpoint, const std::string& gossipEndpoint, const bool& isGossipBind,
                         const std::string& zyreNodeId, const std::unique_ptr<std::unordered_map<std::string, std::string>>& headerKeyValuePairs);
    
    bool
    terminate();
    
    /** \brief Send Zyre unicast message to another (external) entity.
     * 
     * @param zyreRemoteUuid Zyre UUID used to address unicast message (recommend std::move for efficiency)
     * @param messagePayload data that is sent (recommend std::move for efficiency)
     */
    void
    sendZyreWhisperMessage(const std::string& zyreRemoteUuid, const std::string& messagePayload);
    
protected:
    
    virtual
    void
    processReceivedZyreEnterMessage(const std::string& zyreRemoteUuid, const std::unordered_map<std::string, std::string>& headerKeyValuePairs);

    virtual
    void
    processReceivedZyreExitMessage(const std::string& zyreRemoteUuid);
    
    virtual
    void
    processReceivedZyreWhisperMessage(const std::string& zyreRemoteUuid, const std::string& messagePayload);
    
private:

    void
    terminateZyreNodeAndThread();

    void
    executeZyreEventProcessing();

    std::mutex m_mutex;
    bool m_isStarted{true};
    std::unique_ptr<std::thread> m_zyreEventProcessingThread;
    std::atomic<bool> m_isTerminate{false};

    /** \brief Specifies network device used by zyre for communication */
	std::string m_zyreNetworkDevice = std::string("wlan0");
   // the zyre endpoint for use with gossip. If not empty, gossip will be used for discovery
	std::string m_zyreEndpoint = std::string();
    // the "well known" gossip end point
	std::string m_gossipEndpoint = std::string();
    // should this instance of zyre bind (or connect) to the gossip endpoint
	bool m_isGossipBind{false};
    std::string m_zyreNodeId;
    zyre_t* m_zyreNode{nullptr};
    
    std::set<std::string> m_receivedMessageHeaderKeys;
    
    bool m_isZyreEnterMessageHandler{false};
    std::function<void(const std::string& zyreRemoteUuid, const std::unordered_map<std::string, std::string>& headerKeyValuePairs)> m_zyreEnterMessageHandler;
    bool m_isZyreExitMessageHandler{false};
    std::function<void(const std::string& zyreRemoteUuid)> m_zyreExitMessageHandler;
    bool m_isZyreWhisperMessageHandler{false};
    std::function<void(const std::string& zyreRemoteUuid, const std::string& messagePayload)> m_zyreWhisperMessageHandler;
    
};

}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_ZERO_MQ_ZYRE_BRIDGE_H */


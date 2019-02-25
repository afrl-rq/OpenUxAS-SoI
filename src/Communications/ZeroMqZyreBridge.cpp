// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ZeroMqZyreBridge.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"

#include "stdUniquePtr.h"

#if (defined(__APPLE__) && defined(__MACH__))
#define OSX
#endif

#ifdef OSX
#include <unistd.h>
#include <sys/select.h>
#include <termios.h>
#include <set>
#elif (!defined(WIN32))
#include <unistd.h>
#include <sys/select.h>
#include <termio.h>
#include <set>
#endif

namespace uxas
{
namespace communications
{

ZeroMqZyreBridge::ZeroMqZyreBridge()
{
};

ZeroMqZyreBridge::~ZeroMqZyreBridge()
{
    m_isStarted = false;
    m_isTerminate = true;
    terminateZyreNodeAndThread();
};

void
ZeroMqZyreBridge::setZyreEnterMessageHandler(std::function<void(const std::string& zyreRemoteUuid, const std::unordered_map<std::string, std::string>& headerKeyValuePairs)>&& zyreEnterMessageHandler)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    m_zyreEnterMessageHandler = std::move(zyreEnterMessageHandler);
    m_isZyreEnterMessageHandler = true;
};

void
ZeroMqZyreBridge::setZyreExitMessageHandler(std::function<void(const std::string& zyreRemoteUuid)>&& zyreExitMessageHandler)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    m_zyreExitMessageHandler = std::move(zyreExitMessageHandler);
    m_isZyreExitMessageHandler = true;
};

void
ZeroMqZyreBridge::setZyreWhisperMessageHandler(std::function<void(const std::string& zyreRemoteUuid, const std::string& messagePayload)>&& zyreWhisperMessageHandler)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    m_zyreWhisperMessageHandler = std::move(zyreWhisperMessageHandler);
    m_isZyreWhisperMessageHandler = true;
};

bool
ZeroMqZyreBridge::start(const std::string& zyreNetworkDevice, const std::string& zyreEndpoint, const std::string& gossipEndpoint, const bool& isGossipBind,
                         const std::string& zyreNodeId, const std::unique_ptr<std::unordered_map<std::string, std::string>>& headerKeyValuePairs)
{
    bool useGossip = false;
    
    if (!zyreEndpoint.empty() && !gossipEndpoint.empty())
    {
        useGossip = true;
        m_zyreEndpoint = zyreEndpoint;
        m_gossipEndpoint = gossipEndpoint;
        m_isGossipBind = isGossipBind;
        UXAS_LOG_INFORM(s_typeName(), "::configure reading Zyre endpoint value ", zyreEndpoint);
        UXAS_LOG_INFORM(s_typeName(), "::configure reading Zyre gossip endpoint value ", gossipEndpoint);
    }
    else if (!zyreNetworkDevice.empty())
    {
        m_zyreNetworkDevice = zyreNetworkDevice;
        UXAS_LOG_INFORM(s_typeName(), "::start set Zyre network device to ", m_zyreNetworkDevice);
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::start failed due to invalid Zyre network device function parameter");
        return (false);
    }
    if (!zyreNodeId.empty())
    {
        m_zyreNodeId = zyreNodeId;
        UXAS_LOG_INFORM(s_typeName(), "::start set Zyre node ID to ", m_zyreNodeId);
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::start failed due to invalid Zyre node ID function parameter");
        return (false);
    }
    
    std::unique_lock<std::mutex> lock(m_mutex);
    m_isStarted = false;
    m_isTerminate = true;
    lock.unlock();
    lock.lock();
    terminateZyreNodeAndThread();

    m_zyreNode = zyre_new(m_zyreNodeId.c_str());
    if(!useGossip)
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::start creating new Zyre node with node ID ", m_zyreNodeId, " and network device ", m_zyreNetworkDevice);
        zyre_set_interface(m_zyreNode, m_zyreNetworkDevice.c_str()); // associate node with network device
    }
    else
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::start creating new Zyre node with node ID ", m_zyreNodeId, " zyre endpoint ", zyreEndpoint, " and gossip endpoint ", gossipEndpoint);
        zyre_set_endpoint(m_zyreNode, "%s", m_zyreEndpoint.c_str());
        if(m_isGossipBind)
        {
            zyre_gossip_bind(m_zyreNode, "%s", m_gossipEndpoint.c_str());
        }
        else
        {
            zyre_gossip_connect(m_zyreNode, "%s", m_gossipEndpoint.c_str());
        }
    }

    for (auto hdrKvPairsIt = headerKeyValuePairs->cbegin(), hdrKvPairsItEnd = headerKeyValuePairs->cend(); hdrKvPairsIt != hdrKvPairsItEnd; hdrKvPairsIt++)
    {
        UXAS_LOG_INFORM(s_typeName(), "::start adding header key/value pair KEY [", hdrKvPairsIt->first, "] VALUE [", hdrKvPairsIt->second, "]");
        n_ZMQ::zyreSetHeaderEntry(m_zyreNode, hdrKvPairsIt->first, hdrKvPairsIt->second);
        m_receivedMessageHeaderKeys.emplace(hdrKvPairsIt->first.substr());
    }
    
    int zyreNodeStartRtnCode = zyre_start(m_zyreNode);
    if (zyreNodeStartRtnCode == 0)
    {
        m_isStarted = true;
        m_isTerminate = false;
        m_zyreEventProcessingThread = uxas::stduxas::make_unique<std::thread>(&ZeroMqZyreBridge::executeZyreEventProcessing, this);
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::start Zyre event processing thread [", m_zyreEventProcessingThread->get_id(), "]");
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::start failed at Zyre node zyre_start function call");
        return (false);
    }
    
    // un-comment the following line for debugging Zyre
    //zyre_set_verbose(m_zyreNode);
    //n_ZMQ::zyreJoin(m_zyreNode, m_zyreGroup); // group enables Zyre multicast, m_zyreNode is unique ID for a single Zyre node
    UXAS_LOG_INFORM(s_typeName(), "::start started Zyre node with node ID ", m_zyreNodeId, " and network device ", m_zyreNetworkDevice);
    return (true);
};

bool
ZeroMqZyreBridge::terminate()
{
    std::unique_lock<std::mutex> lock(m_mutex);
    m_isStarted = false;
    m_isTerminate = true;
    lock.unlock();
    lock.lock();
    terminateZyreNodeAndThread();
    return (true);
};

void
ZeroMqZyreBridge::terminateZyreNodeAndThread()
{
    try
    {
        if (m_zyreNode != nullptr)
        {
            zyre_destroy(&m_zyreNode);
            m_zyreNode = nullptr;
            UXAS_LOG_INFORM(s_typeName(), "::terminateZyreNodeAndThread destroyed Zyre node");
        }
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR(s_typeName(), "::terminateZyreNodeAndThread destroying Zyre node EXCEPTION: ", ex.what());
    }

    if (m_zyreEventProcessingThread && m_zyreEventProcessingThread->joinable())
    {
        m_zyreEventProcessingThread->detach();
        UXAS_LOG_INFORM(s_typeName(), "::terminateZyreNodeAndThread detached m_zyreEventProcessingThread");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::terminateZyreNodeAndThread did not detach m_zyreEventProcessingThread");
    }
};

void
ZeroMqZyreBridge::executeZyreEventProcessing()
{
    try
    {
        // create a poller and add Zyre node reader
        zpoller_t *poller = zpoller_new(zyre_socket(m_zyreNode), NULL);
        assert(poller);

        while (!m_isTerminate)
        {
            std::unique_lock<std::mutex> lock(m_mutex);
            if (m_isStarted)
            {
                // wait indefinitely for the next input on returned reader
                zsock_t *readerWithNextInput = (zsock_t *) zpoller_wait(poller, uxas::common::ConfigurationManager::getZeroMqReceiveSocketPollWaitTime_ms());

                // affirm reader input is Zyre node reader and process
                if (readerWithNextInput == zyre_socket(m_zyreNode))
                {
                    zyre_event_t *zyre_event = zyre_event_new(m_zyreNode);

                    if (strcmp(zyre_event_type(zyre_event),"ENTER") == 0)
                    {
                        // <editor-fold defaultstate="collapsed" desc="ZYRE_EVENT_ENTER">
                        std::string zyreRemoteUuid(static_cast<const char*> (zyre_event_peer_uuid(zyre_event)));
                        UXAS_LOG_INFORM(s_typeName(), "::executeZyreEventProcessing ZYRE_EVENT_ENTER event from ", zyreRemoteUuid);
                        if (!zyreRemoteUuid.empty())
                        {
                            if (m_isZyreEnterMessageHandler)
                            {
                                std::unordered_map<std::string, std::string> headerKeyValuePairs;
                                zhash_t *headers = zyre_event_headers(zyre_event);
                                if (headers)
                                {
                                    for (auto hdrKeysIt = m_receivedMessageHeaderKeys.cbegin(), hdrKvPairsItEnd = m_receivedMessageHeaderKeys.cend(); hdrKeysIt != hdrKvPairsItEnd; hdrKeysIt++)
                                    {
                                        std::string value;
                                        n_ZMQ::ZhashLookup(headers, hdrKeysIt->substr(), value);
                                        UXAS_LOG_INFORM(s_typeName(), "::executeZyreEventProcessing received ZYRE_EVENT_ENTER header key/value pair KEY [", hdrKeysIt->substr(), "] VALUE [", value, "]");
                                        headerKeyValuePairs.emplace(hdrKeysIt->substr(), std::move(value));
                                    }
                                }
                                headers = nullptr; // release borrowed headers (hash) object
                                UXAS_LOG_DEBUGGING(s_typeName(), "::executeZyreEventProcessing invoking Zyre enter message handler");
                                processReceivedZyreEnterMessage(zyreRemoteUuid, headerKeyValuePairs);
                            }
                            else
                            {
                                UXAS_LOG_WARN(s_typeName(), "::executeZyreEventProcessing not invoking Zyre enter message handler - callback function not set");
                            }
                        }
                        else
                        {
                            UXAS_LOG_WARN(s_typeName(), "::executeZyreEventProcessing ignoring ZYRE_EVENT_EXIT event having empty remote UUID");
                        }
                        // </editor-fold>
                    }
                    else if (strcmp(zyre_event_type(zyre_event), "JOIN") == 0)
                    {
                        UXAS_LOG_INFORM(s_typeName(), "::executeZyreEventProcessing ignoring ZYRE_EVENT_JOIN event from ",
                                 static_cast<const char*> (zyre_event_peer_uuid(zyre_event)));
                    }
                    else if (strcmp(zyre_event_type(zyre_event), "LEAVE") == 0)
                    {
                        UXAS_LOG_INFORM(s_typeName(), "::executeZyreEventProcessing ignoring ZYRE_EVENT_LEAVE event from ",
                                 static_cast<const char*> (zyre_event_peer_uuid(zyre_event)));
                    }
                    else if (strcmp(zyre_event_type(zyre_event), "EXIT") == 0)
                    {
                        // <editor-fold defaultstate="collapsed" desc="ZYRE_EVENT_EXIT">
                        std::string zyreRemoteUuid(static_cast<const char*> (zyre_event_peer_uuid(zyre_event)));
                        if (!zyreRemoteUuid.empty())
                        {
                            if (m_isZyreExitMessageHandler)
                            {
                                UXAS_LOG_INFORM(s_typeName(), "::executeZyreEventProcessing ZYRE_EVENT_EXIT event from ", zyreRemoteUuid, " invoking Zyre exit message handler");
                                processReceivedZyreExitMessage(zyreRemoteUuid);
                            }
                            else
                            {
                                UXAS_LOG_WARN(s_typeName(), "::executeZyreEventProcessing not invoking Zyre exit message handler - callback function not set");
                            }
                        }
                        else
                        {
                            UXAS_LOG_WARN(s_typeName(), "::executeZyreEventProcessing ignoring ZYRE_EVENT_EXIT event having empty remote UUID");
                        }
                        // </editor-fold>
                    }
                    else if (strcmp(zyre_event_type(zyre_event), "SHOUT") == 0)
                    {
                        UXAS_LOG_INFORM(s_typeName(), "::executeZyreEventProcessing ignoring ZYRE_EVENT_SHOUT event from ",
                                 static_cast<const char*> (zyre_event_peer_uuid(zyre_event)));
                    }
                    else if (strcmp(zyre_event_type(zyre_event), "WHISPER") == 0)
                    {
                        // <editor-fold defaultstate="collapsed" desc="ZYRE_EVENT_WHISPER">
                        std::string zyreRemoteUuid(static_cast<const char*> (zyre_event_peer_uuid(zyre_event)));
                        if (!zyreRemoteUuid.empty())
                        {
                            zmsg_t *msg = zyre_event_msg(zyre_event);
                            std::string messagePayload;
                            n_ZMQ::zmsgPopstr(msg, messagePayload);
                            msg = nullptr; // release borrowed message object
                            if (!messagePayload.empty())
                            {
                                UXAS_LOG_INFORM(s_typeName(), "::executeZyreEventProcessing ZYRE_EVENT_WHISPER event from ", zyreRemoteUuid);
                                UXAS_LOG_DEBUGGING(s_typeName(), "::executeZyreEventProcessing ZYRE_EVENT_WHISPER event from ",
                                              zyreRemoteUuid, " with message payload ", messagePayload);
                                if (m_isZyreWhisperMessageHandler)
                                {
                                    UXAS_LOG_DEBUGGING(s_typeName(), "::executeZyreEventProcessing invoking Zyre whisper message handler");
                                    processReceivedZyreWhisperMessage(zyreRemoteUuid, messagePayload);
                                }
                                else
                                {
                                    UXAS_LOG_WARN(s_typeName(), "::executeZyreEventProcessing not invoking Zyre whisper message handler - callback function not set");
                                }
                            }
                            else
                            {
                                UXAS_LOG_ERROR(s_typeName(), "::executeZyreEventProcessing ignoring invalid ZYRE_EVENT_WHISPER event having empty message payload");
                            }
                        }
                        else
                        {
                            UXAS_LOG_WARN(s_typeName(), "::executeZyreEventProcessing ignoring ZYRE_EVENT_WHISPER event having empty remote UUID");
                        }
                        // </editor-fold>
                    }
                    zyre_event_destroy(&zyre_event);
                }
            }
            else
            {
                int rc = zpoller_remove(poller, zyre_socket(m_zyreNode));
                assert(rc == 0);
                zpoller_destroy(&poller);
                break;
            }
        }
        UXAS_LOG_INFORM(s_typeName(), "::executeTcpReceiveProcessing exiting infinite loop thread [", std::this_thread::get_id(), "]");
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR(s_typeName(), "::executeZyreEventProcessing EXCEPTION: ", ex.what());
    }
};

void
ZeroMqZyreBridge::processReceivedZyreEnterMessage(const std::string& zyreRemoteUuid, const std::unordered_map<std::string, std::string>& headerKeyValuePairs)
{
    UXAS_LOG_INFORM(s_typeName(), "::processReceivedZyreEnterMessage invoking registered handler");
    m_zyreEnterMessageHandler(zyreRemoteUuid, headerKeyValuePairs);
};

void
ZeroMqZyreBridge::processReceivedZyreExitMessage(const std::string& zyreRemoteUuid)
{
    UXAS_LOG_INFORM(s_typeName(), "::processReceivedZyreExitMessage invoking registered handler");
    m_zyreExitMessageHandler(zyreRemoteUuid);
};

void
ZeroMqZyreBridge::processReceivedZyreWhisperMessage(const std::string& zyreRemoteUuid, const std::string& messagePayload)
{
    UXAS_LOG_INFORM(s_typeName(), "::processReceivedZyreWhisperMessage invoking registered handler");
    m_zyreWhisperMessageHandler(zyreRemoteUuid, messagePayload);
};

void
ZeroMqZyreBridge::sendZyreWhisperMessage(const std::string& zyreRemoteUuid, const std::string& messagePayload)
{
    UXAS_LOG_INFORM(s_typeName(), "::sendZyreWhisperMessage sending Zyre whisper message");
    n_ZMQ::zyreWhisper2(m_zyreNode, zyreRemoteUuid, messagePayload);
};

}; //namespace communications
}; //namespace uxas


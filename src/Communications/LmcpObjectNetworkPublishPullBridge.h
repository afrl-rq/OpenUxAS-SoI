// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_NETWORK_ZEROMQ_PUBLISH_PULL_BRIDGE_H
#define UXAS_MESSAGE_LMCP_OBJECT_NETWORK_ZEROMQ_PUBLISH_PULL_BRIDGE_H

#include "LmcpObjectMessageReceiverPipe.h"
#include "LmcpObjectMessageSenderPipe.h"
#include "LmcpObjectNetworkClientBase.h"

#include <atomic>
#include <cstdint>

namespace uxas
{
namespace communications
{

class LmcpObjectNetworkPublishPullBridge : public LmcpObjectNetworkClientBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("LmcpObjectNetworkPublishPullBridge"); return (s_string); };

    LmcpObjectNetworkPublishPullBridge();

    ~LmcpObjectNetworkPublishPullBridge();

private:

    /** \brief Copy construction not permitted */
    LmcpObjectNetworkPublishPullBridge(LmcpObjectNetworkPublishPullBridge const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectNetworkPublishPullBridge const&) = delete;

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
    std::set<std::string> m_nonImportForwardAddresses;
    std::set<std::string> m_nonExportForwardAddresses;

    uxas::communications::LmcpObjectMessageSenderPipe m_externalLmcpObjectMessageSenderPipe;

    std::string m_externalPullSocketAddress = std::string("tcp://*:5555");
    std::string m_externalPublishSocketAddress = std::string("tcp://*:5556");
};

}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_LMCP_OBJECT_NETWORK_ZEROMQ_PUBLISH_PULL_BRIDGE_H */


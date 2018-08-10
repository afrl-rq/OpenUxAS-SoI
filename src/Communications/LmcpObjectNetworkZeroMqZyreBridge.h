// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_NETWORK_ZERO_MQ_ZYRE_BRIDGE_H
#define    UXAS_MESSAGE_LMCP_OBJECT_NETWORK_ZERO_MQ_ZYRE_BRIDGE_H

#include "LmcpObjectNetworkClientBase.h"
#include "ZeroMqZyreBridge.h"

#include "UxAS_SentinelSerialBuffer.h"

#include <thread>
#include <memory>
#include <mutex>
#include <unordered_map>
#include <vector>

namespace uxas
{
namespace communications
{

/** \class LmcpObjectNetworkZeroMqZyreBridge
    \brief A service that provides network discovery and communications.
 * Dynamically discovers and bridges with zero-many Zyre-enabled systems.
 * 
 * 
 * 
 * </ul> @n
 * 
 * 
 * 
 * 
 */

/*
 * DESIGN 20151201 dbk, rjt
 * VICS interface service - no pause/resume
 * 1. Request/response behavior
 * 2. VICS interface hosted by UGS will send response to each internal query 
 * message from bridge (accepting that this can result in duplicated local messages 
 * for case of multiple UAVs connected that make similar/same request).
 * 3. Access requirement for address subscription to be conditional to one or both
 * sides of zyre connection.  Prefer agnostic address subscription.
 * 3.a. Question: What messages are needed by UAV from other UAVs?
 * 3.b. Question: What messages are needed by UAV from UGSs?
 * 3.c. Question: What messages are needed by UGSs from other UGSs?
 * 3.d. Question: What messages are needed by UGSs from UAVs?
 * 
 * 
   // generates a new VicsEntityType value for the passed string
   static VicsEntityType get_VicsEntityType(std::string str) {
       if ( str == "Unknown") return Unknown;
       if ( str == "VSCS_Ground") return VSCS_Ground;
       if ( str == "Dismount") return Dismount;
       if ( str == "Aircraft") return Aircraft;
       if ( str == "UGS") return UGS;
        return Unknown;

   }

20151203, 20160105 dbk, rjt

UAV msg-> UAV (implies UAV external zyre subscriptions)
  IsolationCoordination
  BandwidthTest

UGS msg-> UAV (implies UAV external zyre subscriptions)
  QueryResponse
  IntruderAlert
  VicsAck ?? (review/affirm rqmt)
  BandwidthTest

UAV msg-> UGS (implies UGS external zyre subscriptions)
  MessageQuery
  VicsAck ?? (review/affirm rqmt)
  BandwidthTest

user_laptop msg-> UGS (implies UGS external zyre subscriptions)
  RadarEnableMessage
  UgsConfiguration
  UgsStatusRequest
  MessageQuery
  VicsAck ?? (review/affirm rqmt)
  IntruderAlert // enables intruder simulation via IntruderAlert message injection from a laptop

UGS msg-> user_laptop (implies user_laptop external zyre subscriptions)
  QueryResponse
  IntruderAlert
  VicsAck ?? (review/affirm rqmt)
  UgsStatusResponse



// TRIVIAL CASE
UGS msg-> UGS
<none>
=> UGS external zyre subscription to:
    //empty_set


20151207 dbk, rjt: user laptop entity type is ... hmmmm ... ???
'... looks like aircraft ...'

UserLaptopAircraft

   // generates a new VicsEntityType value for the passed string
   static VicsEntityType get_VicsEntityType(std::string str) {
       if ( str == "Unknown") return Unknown;
       if ( str == "VSCS_Ground") return VSCS_Ground;
       if ( str == "Dismount") return Dismount;
       if ( str == "Aircraft") return Aircraft;
       if ( str == "UGS") return UGS;
        return Unknown;

   }

 * 
 * 
 * 
 * 
 * 
<!-- LmcpObjectNetworkZeroMqZyreBridge

DESIGN 20160105 dbk, rjt - messaging

GUARD AGAINST MESSAGE BOOMERANGING
services ignore messages sent by it (require msgEId != svcEId or msgSvcId != svcSvcId to proceed with processing)
entity bridges ignore external messages it sent (require extMsgEId != bridgeEId to forward-send onto internal bus)
entity bridges ignore internal messages that came from an external entity (require msgEId == bridgeEId to forward-send out across Zyre)
bridge does not support entity-entity communication forwarding

ZYRE BRIDGE - CONNECTION LIFECYCLE
message subscriptions are not entity specific (this implementation can be extended to effect this behavior)
Zyre EntityEnter message header contains entityId, serviceId, message subscriptions (defined in UxAS cfg.xml files)
Zyre EntityEnter event includes sending EntityJoin message onto local bus
Zyre EntityExit event defines end of entity-entity communication 
Zyre EntityExit event includes sending EntityExit message onto local bus

SPECIAL CASE - LAPTOP INTRUDER SIMULATION
all entities host a VICS Interface Service
for every received IntruderAlert message, VICS Interface Services will:
1. check if received message was previously received (check entityId and messageId fields).  If previously received, then ignore - else perform steps 2 and 3.
2. store the IntruderAlert message (composite key: entityId, messageId).
3. re-send (forward) IntruderAlert message after setting entityId and serviceId message fields with its own ID values (no change to originator entityId, messageId fields).
DBK & RJT recognize that limited, unnecessary messaging will occur (accepted since laptop intruder simulation is infrequent and low bandwidth)

-->        
        <Bridge Type="LmcpObjectNetworkZeroMqZyreBridge" ><!-- UAV -->
            <SubscribeToExternalMessage MessageType="uxas.messages.native.BandwidthTest" />
            <SubscribeToExternalMessage MessageType="uxas.project.isolate.IntruderAlert" />
            <SubscribeToExternalMessage MessageType="uxas.project.isolate.IsolationCoordination" />
            <SubscribeToExternalMessage MessageType="uxas.project.vics.QueryResponse" />
            <SubscribeToExternalMessage MessageType="uxas.project.vics.VicsAck" />
        </Bridge>
        <Bridge Type="LmcpObjectNetworkZeroMqZyreBridge" ><!-- UGS -->
            <SubscribeToExternalMessage MessageType="uxas.messages.native.BandwidthTest" />
            <SubscribeToExternalMessage MessageType="uxas.project.isolate.IntruderAlert" /><!-- enables intruder simulation via IntruderAlert message injection from a laptop -->
            <SubscribeToExternalMessage MessageType="uxas.project.vics.MessageQuery" />
            <SubscribeToExternalMessage MessageType="uxas.project.vics.RadarEnableMessage" />
            <SubscribeToExternalMessage MessageType="uxas.project.vics.UgsConfiguration" />
            <SubscribeToExternalMessage MessageType="uxas.project.vics.UgsStatusRequest" />
            <SubscribeToExternalMessage MessageType="uxas.project.vics.VicsAck" />
       </Bridge>
        <Bridge Type="LmcpObjectNetworkZeroMqZyreBridge" ><!-- laptop -->
            <SubscribeToExternalMessage MessageType="uxas.project.isolate.IntruderAlert" />
            <SubscribeToExternalMessage MessageType="uxas.project.vics.QueryResponse" />
            <SubscribeToExternalMessage MessageType="uxas.project.vics.UgsStatusResponse" />
            <SubscribeToExternalMessage MessageType="uxas.project.vics.VicsAck" />
        </Bridge>


 * 
 * 
 * 
 */

//TODO review local service pause/resume
class LmcpObjectNetworkZeroMqZyreBridge final : public LmcpObjectNetworkClientBase
{

public:

    static const std::string&
    s_typeName() { static std::string s_string("LmcpObjectNetworkZeroMqZyreBridge"); return (s_string); };
   
    LmcpObjectNetworkZeroMqZyreBridge();
    
    ~LmcpObjectNetworkZeroMqZyreBridge();

private:

    /** \brief Copy construction not permitted */
    LmcpObjectNetworkZeroMqZyreBridge(LmcpObjectNetworkZeroMqZyreBridge const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectNetworkZeroMqZyreBridge const&) = delete;

public:

    bool
    configure(const pugi::xml_node& bridgeXmlNode) override;
    
private:
    
    bool
    start() override;

    bool
    terminate() override;
    
    bool
    processReceivedSerializedLmcpMessage(
            std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
            receivedLmcpMessage) override;

    void
    zyreEnterMessageHandler(const std::string& zyreRemoteUuid, const std::unordered_map<std::string, std::string>& headerKeyValuePairs);

    void
    zyreExitMessageHandler(const std::string& zyreRemoteUuid);

    void
    zyreWhisperMessageHandler(const std::string& zyreRemoteUuid, const std::string& messagePayload);

    std::mutex m_mutex;
    ZeroMqZyreBridge m_zeroMqZyreBridge;
    
	std::string m_zyreNetworkDevice = std::string("wlan0");
   // the zyre endpoint for use with gossip. If not empty, gossip will be used for discovery
	std::string m_zyreEndpoint = std::string();
    // the "well known" gossip end point
	std::string m_gossipEndpoint = std::string();
    // should this instance of zyre bind (or connect) to the gossip endpoint
	bool m_isGossipBind{false};
    std::unique_ptr<std::unordered_map<std::string, std::string>> m_headerKeyValuePairs;
	std::string m_extSubAddressDelimiter = std::string(";");
    
    uxas::common::SentinelSerialBuffer m_receiveZyreDataBuffer;
    
    std::unordered_map<std::string, std::pair<std::string, std::string>> m_remoteEntityTypeIdsByZyreUuids;
    std::unordered_map<std::string, std::set<std::string>> m_remoteZyreUuidsBySubscriptionAddress;

    std::set<std::string> m_initialPersistentLocalSubscriptionAddresses;
    std::set<std::string> m_nonImportForwardAddresses;
    std::set<std::string> m_nonExportForwardAddresses;
    bool m_isConsideredSelfGenerated{false};
};

}; //namespace communications
}; //namespace uxas

#endif    /* UXAS_MESSAGE_LMCP_OBJECT_NETWORK_ZERO_MQ_ZYRE_BRIDGE_H */

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_IMPACT_SUBSCRIBE_PUSH_BRIDGE_H
#define UXAS_MESSAGE_IMPACT_SUBSCRIBE_PUSH_BRIDGE_H

#include "LmcpObjectMessageReceiverPipe.h"
#include "LmcpObjectMessageSenderPipe.h"
#include "LmcpObjectNetworkClientBase.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"

#include <atomic>
#include <cstdint>

namespace uxas
{
  namespace communications
  {

    /** \class ImpactSubscribePushBridge
     *  \brief A component that connects an external entity to the internal message
     * bus using <I>ZMQ_SUB<I/> and <I>ZMQ_PUSH<I/> sockets. Uses two part messages
     * with IMPACT addressing (i.e. 'lmcp:[MDM SERIES NAME]:[message type name]')
     * and reports group as 'fusion'
     *
     *
     *  @par Description:
     * The <B>Subscribe/Push Bridge<B/> component connects to external entities using
     * <I>ZMQ_SUB<I/> and <I>ZMQ_PUSH<I/> sockets. The external entity sends messages to the
     * <B>Subscribe/Push Bridge<B/> using a ZeroMQ PUB socket and receives messages using
     * a PULL socket. The the <B>Subscribe/Push Bridge<B/> sends messages received from
     * the external entity to the local @ref c_CommunicationHub. Subscribed messages
     * received from the local @ref c_CommunicationHub are sent to the external entity.
     *
     * @par Example:
     * <Bridge Type="ImpactSubscribePushBridge"
     *    AddressSUB="tcp://localhost:6561"
     *    AddressPUSH="tcp://localhost:6562"
     *    ExternalID=entityID
     *    ThrottleConfigurationForwarding="false"
     *    ConsiderSelfGenerated="false">
     *
     * AddressSUB: the address and port for the ZeroMQ subscription connection
     * AddressPUSH: the address and port for the ZeroMQ push connection
     * ExternalID: the entity ID for which this connection should report all traffic as originating from
     * ThrottleConfigurationForwarding: boolean that when true prevents duplicate air vehicle configurations from being forwarded
     * ConsiderSelfGenerated: boolean that when true overwrites the external ID with local ID
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

    class ImpactSubscribePushBridge : public LmcpObjectNetworkClientBase
    {
    public:

      static const std::string&
        s_typeName() { static std::string s_string("ImpactSubscribePushBridge"); return (s_string); };

      ImpactSubscribePushBridge();

      ~ImpactSubscribePushBridge();

    private:

      /** \brief Copy construction not permitted */
      ImpactSubscribePushBridge(ImpactSubscribePushBridge const&) = delete;

      /** \brief Copy assignment operation not permitted */
      void operator=(ImpactSubscribePushBridge const&) = delete;

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

      std::atomic<bool> m_isTerminate{ false };

      /** \brief External receive processing thread.  */
      std::unique_ptr<std::thread> m_externalReceiveProcessingThread;


      std::set<std::string> m_externalSubscriptionAddresses;
      std::set<std::string> m_nonImportForwardAddresses;
      std::set<std::string> m_nonExportForwardAddresses;

      std::string m_externalSubscribeSocketAddress = std::string("tcp://*:5555");
      std::string m_externalPushSocketAddress = std::string("tcp://*:5556");

      std::unique_ptr<zmq::socket_t> sender;
      std::unique_ptr<zmq::socket_t> subscriber;

      std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::AirVehicleConfiguration> > m_configs;
      bool m_throttleConfigurationForwarding{ false };
      bool m_isConsideredSelfGenerated{ false };
      int64_t m_externalID{0};

    };

  }; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_IMPACT_SUBSCRIBE_PUSH_BRIDGE_H */


// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================


#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"

#include "avtas/lmcp/Factory.h"


#include <sstream>
#include <iostream>
#include <locale>
#include "ZeroMqFabric.h"
#include "ImpactSubscribePushBridge.h"

#define STRING_XML_SUBSCRIBE_TO_EXTERNAL_MESSAGE "SubscribeToExternalMessage"

#define STRING_XML_ADDRESS_SUB "AddressSUB"
#define STRING_XML_ADDRESS_PUSH "AddressPUSH"
#define STRING_XML_EXTERNAL_ENTITY_ID "ExternalID"

namespace uxas
{
  namespace communications
  {

    ImpactSubscribePushBridge::ImpactSubscribePushBridge()
    {
    };

    ImpactSubscribePushBridge::~ImpactSubscribePushBridge()
    {
      if (m_externalReceiveProcessingThread && m_externalReceiveProcessingThread->joinable())
      {
        m_externalReceiveProcessingThread->detach();
      }
    };

    bool
      ImpactSubscribePushBridge::configure(const pugi::xml_node& bridgeXmlNode)
    {
      bool isSuccess{ true };

      if (!bridgeXmlNode.attribute(STRING_XML_ADDRESS_SUB).empty())
      {
        m_externalSubscribeSocketAddress = bridgeXmlNode.attribute(STRING_XML_ADDRESS_SUB).value();
        LOG_INFORM(s_typeName(), "::configure setting external subscribe socket address to ", m_externalSubscribeSocketAddress, " from XML configuration");
      }
      else
      {
        LOG_INFORM(s_typeName(), "::configure failed to find external subscribe socket address in XML configuration; external subscribe socket address is ", m_externalSubscribeSocketAddress);
      }

      if (!bridgeXmlNode.attribute(STRING_XML_ADDRESS_PUSH).empty())
      {
        m_externalPushSocketAddress = bridgeXmlNode.attribute(STRING_XML_ADDRESS_PUSH).value();
        LOG_INFORM(s_typeName(), "::configure setting external push socket address to ", m_externalPushSocketAddress, " from XML configuration");
      }
      else
      {
        LOG_INFORM(s_typeName(), "::configure failed to find external push socket in XML configuration; external push socket is ", m_externalPushSocketAddress);
      }

      if (!bridgeXmlNode.attribute(uxas::common::StringConstant::Server().c_str()).empty())
      {
        m_isServer = bridgeXmlNode.attribute(uxas::common::StringConstant::Server().c_str()).as_bool();
        LOG_INFORM(s_typeName(), "::configure setting server boolean to ", m_isServer, " from XML configuration");
      }
      else
      {
        LOG_INFORM(s_typeName(), "::configure failed to find server boolean in XML configuration; server boolean is ", m_isServer);
      }
      if (!bridgeXmlNode.attribute(STRING_XML_EXTERNAL_ENTITY_ID).empty())
      {
        externalID = bridgeXmlNode.attribute(STRING_XML_EXTERNAL_ENTITY_ID).value();
      }

      // TODO review IMPACT messaging requirements (need to modify object before sending?)
      // handle mapping of UxAS internal single/multi-part messages to IMPACT single/multi-part messages 
      for (pugi::xml_node currentXmlNode = bridgeXmlNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
      {
        if (uxas::common::StringConstant::SubscribeToMessage() == currentXmlNode.name())
        {
          if (!currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).empty())
          {
            addSubscriptionAddress(currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).value());
          }
        }
        else if (uxas::common::StringConstant::SubscribeToExternalMessage() == currentXmlNode.name())
        {
          if (!currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).empty())
          {
            m_externalSubscriptionAddresses.emplace(currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).value());
          }
        }
      }

      //
      // DESIGN 20150911 RJT message addressing - entity ID
      // - received/sent LMCP messages always include entity ID
      // - the entity cast address is derived from entity ID (see getEntityCastAddress function)
      // - bridges never subscribe to the entity cast address on the internal network
      // - bridges usually subscribe (or coordinate subscription) to the entity cast address on external networks
      //   (TCP and serial bridges do not have external subscription)
      //
      // subscribe to external messages addressed to this entity
      LOG_INFORM(s_typeName(), "::configure externally subscribing to entity cast address [", getEntityCastAddress(m_entityId), "]");
      m_externalSubscriptionAddresses.emplace(getEntityCastAddress(m_entityId));

      // do not forward any uni-cast messages addressed to this bridge
      LOG_INFORM(s_typeName(), "::configure adding non-forward address [", getNetworkClientUnicastAddress(m_entityId, m_networkId), "]");
      m_nonImportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));
      m_nonExportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));

      return (isSuccess);
    };

    bool
      ImpactSubscribePushBridge::initialize()
    {
      int32_t zmqhighWaterMark{ 100000 };

      //push socket
      auto pushConfig = transport::ZeroMqSocketConfiguration(uxas::communications::transport::NETWORK_NAME::zmqLmcpNetwork(),
        m_externalPushSocketAddress, ZMQ_PUSH, false, false, zmqhighWaterMark, zmqhighWaterMark);

      sender = transport::ZeroMqFabric::getInstance().createSocket(pushConfig);


      //sub socket
      auto subConfig = transport::ZeroMqSocketConfiguration(uxas::communications::transport::NETWORK_NAME::zmqLmcpNetwork(),
        m_externalSubscribeSocketAddress, ZMQ_SUB, false, true, zmqhighWaterMark, zmqhighWaterMark);
      subscriber = transport::ZeroMqFabric::getInstance().createSocket(subConfig);
      //subscriber->setsockopt(ZMQ_SUBSCRIBE, "lmcp:", 4);

      //loop through m_externalSubscriptionAddresses
      for (auto externalSubscription : m_externalSubscriptionAddresses)
      {
        subscriber->setsockopt(ZMQ_SUBSCRIBE, externalSubscription.c_str(), externalSubscription.size());
      }

      LOG_INFORM(s_typeName(), "::initialize succeeded");
      return (true);
    };

    bool
      ImpactSubscribePushBridge::start()
    {
      m_externalReceiveProcessingThread = uxas::stduxas::make_unique<std::thread>(&ImpactSubscribePushBridge
        ::executeExternalSerializedLmcpObjectReceiveProcessing, this);
      LOG_INFORM(s_typeName(), "::start subscribe receive processing thread [", m_externalReceiveProcessingThread->get_id(), "]");
      return (true);
    };

    bool
      ImpactSubscribePushBridge::terminate()
    {
      m_isTerminate = true;
      if (m_externalReceiveProcessingThread && m_externalReceiveProcessingThread->joinable())
      {
        m_externalReceiveProcessingThread->join();
        LOG_INFORM(s_typeName(), "::terminate calling thread completed m_externalReceiveProcessingThread join");
      }
      else
      {
        LOG_WARN(s_typeName(), "::terminate unexpectedly could not join m_externalReceiveProcessingThread");
      }

      return (true);
    };

    bool
      ImpactSubscribePushBridge::processReceivedSerializedLmcpMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
        receivedLmcpMessage)
    {

      // send message to the external entity
      LOG_DEBUGGING(s_typeName(), "::processReceivedSerializedLmcpMessage before sending serialized message ",
        "having address ", receivedLmcpMessage->getAddress(),
        " and size ", receivedLmcpMessage->getPayload().size());

      // process messages from a local service (only)
      if (m_entityIdString == receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId())
      {
        if (m_nonExportForwardAddresses.find(receivedLmcpMessage->getAddress()) == m_nonExportForwardAddresses.end())
        {
          LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage processing message with source service ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceServiceId());

          //make header
          std::string ClassName(receivedLmcpMessage->getAddress());
          std::string last(ClassName.substr(ClassName.rfind(".") + 1));


          std::stringstream ss(receivedLmcpMessage->getMessageAttributesReference()->getDescriptor());
          std::string seriesName;
          std::getline(ss, seriesName, '.');
          std::getline(ss, seriesName, '.');

          std::locale loc;
          //convert seriesName to uppercase
          for (std::string::size_type i = 0; i < seriesName.length(); i++)
          {
            seriesName[i] = std::toupper(seriesName[i], loc);
          }

          std::string header = "lmcp:" + seriesName + ":" + last;

          n_ZMQ::s_sendmore(*sender, header);
          n_ZMQ::s_send(*sender, receivedLmcpMessage->getPayload());


        }
        else
        {
          LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage ignoring non-export message with address ", receivedLmcpMessage->getAddress(), ", source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceServiceId());
        }
      }
      else
      {
        LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage ignoring message with source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId());
      }

      return (false); // always false implies never terminating bridge from here
    };

    void
      ImpactSubscribePushBridge::executeExternalSerializedLmcpObjectReceiveProcessing()
    {
      try
      {


        while (!m_isTerminate)
        {

          std::string key = n_ZMQ::s_recv(*subscriber);
          std::string message = n_ZMQ::s_recv(*subscriber);


          std::stringstream ss(key);
          std::string LMCPHeader, seriesName, className;

          //parse out the header from the two-part message.
          std::getline(ss, LMCPHeader, ':');
          std::getline(ss, seriesName, ':');
          std::getline(ss, className, ':');

          std::locale loc;
          //convert seriesName to lowercase
          for (std::string::size_type i = 0; i < seriesName.length(); i++)
          {
            seriesName[i] = std::tolower(seriesName[i], loc);
          }

          //build back to the LMCP_FULL_NAME 
          std::string fullName = "afrl." + seriesName + "." + className;

          avtas::lmcp::ByteBuffer byteBuffer;
          byteBuffer.allocate(message.size());
          byteBuffer.put(reinterpret_cast<const uint8_t*>(message.c_str()), message.size());
          byteBuffer.rewind();

          std::shared_ptr<avtas::lmcp::Object> ptr_Object;
          ptr_Object.reset(avtas::lmcp::Factory::getObject(byteBuffer));

          std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> recvdAddAttMsg = uxas::stduxas::make_unique<uxas::communications::data::AddressedAttributedMessage>();

          recvdAddAttMsg->setAddressAttributesAndPayload(fullName, "lmcp", fullName, "fusion", externalID, "1", message);


          // send message to the external entity
          if (recvdAddAttMsg->isValid())
          {
            LOG_DEBUGGING(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing before sending serialized message ",
              "having address ", recvdAddAttMsg->getAddress(),
              " and size ", recvdAddAttMsg->getPayload().size());

            // process messages from an external service (only)
            if (m_entityIdString != recvdAddAttMsg->getMessageAttributesReference()->getSourceEntityId())
            {
              if (m_nonImportForwardAddresses.find(recvdAddAttMsg->getAddress()) == m_nonImportForwardAddresses.end())
              {
                sendSerializedLmcpObjectMessage(std::move(recvdAddAttMsg));
                //LmcpObjectNetworkClientBase::sendSharedLmcpObjectBroadcastMessage(ptr_Object);

              }
              else
              {
                LOG_INFORM(s_typeName(), "::executeSerialReceiveProcessing ignoring non-import message with address ", recvdAddAttMsg->getAddress(), ", source entity ID ", recvdAddAttMsg->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", recvdAddAttMsg->getMessageAttributesReference()->getSourceServiceId());
              }
            }
            else
            {
              LOG_INFORM(s_typeName(), "::executeSerialReceiveProcessing ignoring external message with entity ID ", m_entityIdString, " since it matches its own entity ID");
            }
          }
          else
          {
            LOG_WARN(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing ignoring received, invalid AddressedAttributedMessage object");
          }
        }
        LOG_INFORM(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing exiting infinite loop thread [", std::this_thread::get_id(), "]");
      }
      catch (std::exception& ex)
      {
        LOG_ERROR(s_typeName(), "::executeExternalSerializedLmcpObjectReceiveProcessing EXCEPTION: ", ex.what());
      }
    };

  }; //namespace communications
}; //namespace uxas

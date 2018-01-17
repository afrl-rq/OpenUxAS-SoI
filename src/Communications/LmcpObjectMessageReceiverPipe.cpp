// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectMessageReceiverPipe.h"

#include "LmcpMessage.h"
#include "MessageAttributes.h"
#include "ZeroMqSocketConfiguration.h"

#include "avtas/lmcp/ByteBuffer.h"
#include "avtas/lmcp/Factory.h"

#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"

#include "stdUniquePtr.h"

namespace uxas
{
namespace communications
{

void
LmcpObjectMessageReceiverPipe::initializePull(uint32_t entityId, uint32_t serviceId)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_PULL,
                        uxas::common::LmcpNetworkSocketAddress::strGetInProc_ToMessageHub(), true);
};

void
LmcpObjectMessageReceiverPipe::initializeExternalPull(uint32_t entityId, uint32_t serviceId, 
                                                              const std::string& externalSocketAddress, bool isServer)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_PULL, externalSocketAddress, isServer);
};

void
LmcpObjectMessageReceiverPipe::initializeExternalSubscription(uint32_t entityId, uint32_t serviceId, 
                                                              const std::string& externalSocketAddress, bool isServer)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_SUB, externalSocketAddress, isServer);
};

void
LmcpObjectMessageReceiverPipe::initializeSubscription(uint32_t entityId, uint32_t serviceId)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_SUB,
                        uxas::common::LmcpNetworkSocketAddress::strGetInProc_FromMessageHub(), false);
};

void
LmcpObjectMessageReceiverPipe::initializeStream(uint32_t entityId, uint32_t serviceId, 
                                                   const std::string& socketAddress, bool isServer)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_STREAM, socketAddress, isServer);
};

void
LmcpObjectMessageReceiverPipe::initializeZmqSocket(uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType,
                                          const std::string& socketAddress, bool isServer)
{
    m_entityId = entityId;
    m_serviceId = serviceId;

    // notes about zero mq send and receive high water mark:
    // - in some cases, only one is relevant and other is ignored
    // - in other cases, both high water marks are relevant
    int32_t zmqhighWaterMark{100000};

    uxas::communications::transport::ZeroMqSocketConfiguration
    zmqLmcpNetworkReceiveSocket(uxas::communications::transport::NETWORK_NAME::zmqLmcpNetwork(),
                                  socketAddress,
                                  zmqSocketType,
                                  isServer,
                                  true,
                                  zmqhighWaterMark,
                                  zmqhighWaterMark);

    m_transportReceiver = uxas::stduxas::make_unique<uxas::communications::transport::ZeroMqAddressedAttributedMessageReceiver>(
            (zmqSocketType == ZMQ_STREAM ? true : false));
    m_transportReceiver->initialize(m_entityId, m_serviceId, zmqLmcpNetworkReceiveSocket);
};

bool
LmcpObjectMessageReceiverPipe::addLmcpObjectSubscriptionAddress(const std::string& address)
{
    return (m_transportReceiver->addSubscriptionAddress(address));
};

bool
LmcpObjectMessageReceiverPipe::removeLmcpObjectSubscriptionAddress(const std::string& address)
{
    return (m_transportReceiver->removeSubscriptionAddress(address));
};

bool
LmcpObjectMessageReceiverPipe::removeAllLmcpObjectSubscriptionAddresses()
{
    return (m_transportReceiver->removeAllSubscriptionAddresses());
};

std::unique_ptr<uxas::communications::data::LmcpMessage>
LmcpObjectMessageReceiverPipe::getNextMessageObject()
{
    // get next zero mq message
    // limit attempts on each receiver to one
    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> nextZeroMqMessage
            = m_transportReceiver->getNextMessage();

    // process zero mq message
    // (false implies no message retrieved since receiver "queues" were empty)
    if (nextZeroMqMessage)
    {
        // deserialize
        std::unique_ptr<avtas::lmcp::Object> lmcpObject = deserializeMessage(nextZeroMqMessage->getPayload());
        if (lmcpObject)
        {
            std::unique_ptr<uxas::communications::data::LmcpMessage> lmcpMessage 
                    = uxas::stduxas::make_unique<uxas::communications::data::LmcpMessage>
              (nextZeroMqMessage->getMessageAttributesOwnership(), std::move(lmcpObject));
            return (lmcpMessage);
        }
    }

    // handle empty return case (got empty AddressedAttributedMessage or failed de-serialization)
    // return empty unique pointer
    std::unique_ptr<uxas::communications::data::LmcpMessage> emptyLmcpMessage;
    return (emptyLmcpMessage);
};

std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
LmcpObjectMessageReceiverPipe::getNextSerializedMessage()
{
    return (m_transportReceiver->getNextMessage());
};


std::unique_ptr<avtas::lmcp::Object>
LmcpObjectMessageReceiverPipe::deserializeMessage(const std::string& payload)
{
    std::unique_ptr<avtas::lmcp::Object> lmcpObject;

    // allocate memory
    avtas::lmcp::ByteBuffer lmcpByteBuffer;
    lmcpByteBuffer.allocate(payload.size());
    lmcpByteBuffer.rewind();

    for (size_t charIndex = 0; charIndex < payload.size(); charIndex++)
    {
        lmcpByteBuffer.putByte(payload[charIndex]); // TODO REVIEW
    }
    lmcpByteBuffer.rewind();
    
    lmcpObject.reset(avtas::lmcp::Factory::getObject(lmcpByteBuffer));
    if (!lmcpObject)
    {
        UXAS_LOG_ERROR("LmcpObjectMessageReceiverPipe::deserializeMessage failed to convert message payload string into an LMCP object");
    }

    return (lmcpObject);
};

}; //namespace communications
}; //namespace uxas

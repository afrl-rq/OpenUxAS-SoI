// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectMessageTcpReceiverSenderPipe.h"

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
LmcpObjectMessageTcpReceiverSenderPipe::initializeStream(uint32_t entityId, uint32_t serviceId, const std::string& socketAddress, bool isServer)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_STREAM, socketAddress, isServer);
};

void
LmcpObjectMessageTcpReceiverSenderPipe::initializeZmqSocket(uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType,
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

    m_transportTcpReceiverSender = uxas::stduxas::make_unique<uxas::communications::transport::ZeroMqAddressedAttributedMessageTcpReceiverSender>();
    m_transportTcpReceiverSender->initialize(m_entityId, m_serviceId, zmqLmcpNetworkReceiveSocket);
};

bool
LmcpObjectMessageTcpReceiverSenderPipe::addLmcpObjectSubscriptionAddress(const std::string& address)
{
    return (m_transportTcpReceiverSender->addSubscriptionAddress(address));
};

bool
LmcpObjectMessageTcpReceiverSenderPipe::removeLmcpObjectSubscriptionAddress(const std::string& address)
{
    return (m_transportTcpReceiverSender->removeSubscriptionAddress(address));
};

std::unique_ptr<uxas::communications::data::LmcpMessage>
LmcpObjectMessageTcpReceiverSenderPipe::getNextMessageObject()
{
    // get next zero mq message
    // limit attempts on each receiver to one
    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> nextZeroMqMessage
            = m_transportTcpReceiverSender->getNextMessage();

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
LmcpObjectMessageTcpReceiverSenderPipe::getNextSerializedMessage()
{
    return (m_transportTcpReceiverSender->getNextMessage());
};


std::unique_ptr<avtas::lmcp::Object>
LmcpObjectMessageTcpReceiverSenderPipe::deserializeMessage(const std::string& payload)
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
        UXAS_LOG_ERROR("LmcpObjectMessageTcpReceiverSenderPipe::deserializeMessage failed to convert message payload string into an LMCP object");
    }

    return (lmcpObject);
};

void
LmcpObjectMessageTcpReceiverSenderPipe::sendBroadcastMessage(std::unique_ptr<avtas::lmcp::Object> lmcpObject)
{
    std::string fullLmcpObjectTypeName = lmcpObject->getFullLmcpTypeName();
    sendLimitedCastMessage(fullLmcpObjectTypeName, std::move(lmcpObject));
};

void
LmcpObjectMessageTcpReceiverSenderPipe::sendLimitedCastMessage(const std::string& castAddress, std::unique_ptr<avtas::lmcp::Object> lmcpObject)
{
    avtas::lmcp::ByteBuffer* lmcpByteBuffer = avtas::lmcp::Factory::packMessage(lmcpObject.get(), true);
    std::string serializedPayload = std::string(reinterpret_cast<char*>(lmcpByteBuffer->array()), lmcpByteBuffer->capacity());
    delete lmcpByteBuffer;
    m_transportTcpReceiverSender->sendMessage(castAddress, uxas::common::ContentType::lmcp(), lmcpObject->getFullLmcpTypeName(), serializedPayload);
};

void
LmcpObjectMessageTcpReceiverSenderPipe::sendSerializedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> serializedLmcpObject)
{
    m_transportTcpReceiverSender->sendAddressedAttributedMessage(std::move(serializedLmcpObject));
};

void
LmcpObjectMessageTcpReceiverSenderPipe::sendSharedBroadcastMessage(const std::shared_ptr<avtas::lmcp::Object>& lmcpObject)
{
//    std::string fullLmcpObjectTypeName = lmcpObject->getFullLmcpTypeName();
//    sendSharedLimitedCastMessage(fullLmcpObjectTypeName, lmcpObject);
    sendSharedLimitedCastMessage(lmcpObject->getFullLmcpTypeName(), lmcpObject);
};

void
LmcpObjectMessageTcpReceiverSenderPipe::sendSharedLimitedCastMessage(const std::string& castAddress, const std::shared_ptr<avtas::lmcp::Object>& lmcpObject)
{
    avtas::lmcp::ByteBuffer* byteBuffer = avtas::lmcp::Factory::packMessage(lmcpObject.get(), true);
    std::string serializedPayload = std::string(reinterpret_cast<char*>(byteBuffer->array()), byteBuffer->capacity());
    delete byteBuffer;
    m_transportTcpReceiverSender->sendMessage(castAddress, uxas::common::ContentType::lmcp(), lmcpObject->getFullLmcpTypeName(), serializedPayload);
};

}; //namespace communications
}; //namespace uxas

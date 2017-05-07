// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectMessageSenderPipe.h"

#include "avtas/lmcp/ByteBuffer.h"
#include "avtas/lmcp/Factory.h"

#include "ZeroMqSocketConfiguration.h"

#include "SerialHelper.h"

#include "Constants/UxAS_String.h"

#include "stdUniquePtr.h"

namespace uxas
{
namespace communications
{

void
LmcpObjectMessageSenderPipe::initializePublish(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId)
{
    initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_PUB,
                        uxas::common::LmcpNetworkSocketAddress::strGetInProc_FromMessageHub(), true);
};

void
LmcpObjectMessageSenderPipe::initializeExternalPush(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId, 
                                                    const std::string& externalSocketAddress, bool isServer)
{
    initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_PUSH, externalSocketAddress, isServer);
};

void
LmcpObjectMessageSenderPipe::initializeExternalPub(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId, 
                                                    const std::string& externalSocketAddress, bool isServer)
{
    initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_PUB, externalSocketAddress, isServer);
};

void
LmcpObjectMessageSenderPipe::initializePush(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId)
{
    initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_PUSH,
                        uxas::common::LmcpNetworkSocketAddress::strGetInProc_ToMessageHub(), false);
};

void
LmcpObjectMessageSenderPipe::initializeStream(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId, const std::string& socketAddress, bool isServer)
{
    initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_STREAM, socketAddress, isServer);
};

void
LmcpObjectMessageSenderPipe::initializeZmqSocket(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType,
                                                 const std::string& socketAddress, bool isServer)
{
    m_entityId = entityId;
    m_serviceId = serviceId;

    // notes about zero mq send and receive high water mark:
    // - in some cases, only one is relevant and other is ignored
    // - in other cases, both high water marks are relevant
    int32_t zmqhighWaterMark{100000};

    uxas::communications::transport::ZeroMqSocketConfiguration
    zmqLmcpNetworkSendSocket(uxas::communications::transport::NETWORK_NAME::zmqLmcpNetwork(),
                             socketAddress,
                             zmqSocketType,
                             isServer,
                             false,
                             zmqhighWaterMark,
                             zmqhighWaterMark);

    m_transportSender = uxas::stduxas::make_unique<uxas::communications::transport::ZeroMqAddressedAttributedMessageSender>(
            (zmqSocketType == ZMQ_STREAM ? true : false));
    m_transportSender->initialize(sourceGroup, m_entityId, m_serviceId, zmqLmcpNetworkSendSocket);
};

void
LmcpObjectMessageSenderPipe::sendBroadcastMessage(std::unique_ptr<avtas::lmcp::Object> lmcpObject)
{
    std::string fullLmcpObjectTypeName = lmcpObject->getFullLmcpTypeName();
    sendLimitedCastMessage(fullLmcpObjectTypeName, std::move(lmcpObject));
};

void
LmcpObjectMessageSenderPipe::sendLimitedCastMessage(const std::string& castAddress, std::unique_ptr<avtas::lmcp::Object> lmcpObject)
{
    avtas::lmcp::ByteBuffer* lmcpByteBuffer = avtas::lmcp::Factory::packMessage(lmcpObject.get(), true);
    std::string serializedPayload = std::string(reinterpret_cast<char*>(lmcpByteBuffer->array()), lmcpByteBuffer->capacity());
    delete lmcpByteBuffer;
    m_transportSender->sendMessage(castAddress, uxas::common::ContentType::lmcp(), lmcpObject->getFullLmcpTypeName(), std::move(serializedPayload));
};

void
LmcpObjectMessageSenderPipe::sendSerializedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> serializedLmcpObject)
{
    m_transportSender->sendAddressedAttributedMessage(std::move(serializedLmcpObject));
};

void
LmcpObjectMessageSenderPipe::sendSharedBroadcastMessage(const std::shared_ptr<avtas::lmcp::Object>& lmcpObject)
{
//    std::string fullLmcpObjectTypeName = lmcpObject->getFullLmcpTypeName();
//    sendSharedLimitedCastMessage(fullLmcpObjectTypeName, lmcpObject);
    sendSharedLimitedCastMessage(lmcpObject->getFullLmcpTypeName(), lmcpObject);
};

void
LmcpObjectMessageSenderPipe::sendSharedLimitedCastMessage(const std::string& castAddress, const std::shared_ptr<avtas::lmcp::Object>& lmcpObject)
{
    avtas::lmcp::ByteBuffer* lmcpByteBuffer = avtas::lmcp::Factory::packMessage(lmcpObject.get(), true);
    std::string serializedPayload = std::string(reinterpret_cast<char*>(lmcpByteBuffer->array()), lmcpByteBuffer->capacity());
    delete lmcpByteBuffer;
    m_transportSender->sendMessage(castAddress, uxas::common::ContentType::lmcp(), lmcpObject->getFullLmcpTypeName(), std::move(serializedPayload));
};

}; //namespace communications
}; //namespace uxas

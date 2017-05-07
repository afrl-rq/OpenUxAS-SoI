// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "AddressStringMessageSenderPipe.h"

#include "ZeroMqSocketConfiguration.h"

#include "stdUniquePtr.h"

#include "Constants/Constants_Control.h"

namespace uxas
{
namespace communications
{

void
AddressStringMessageSenderPipe::initializePublish(uint32_t entityId, uint32_t serviceId)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_PUB, 
                        n_Const::c_Constants_Control::strGetInProc_FromMessageHub(), true);    
};

void
AddressStringMessageSenderPipe::initializeExternalPush(uint32_t entityId, uint32_t serviceId, 
                                                       const std::string& externalSocketAddress, bool isServer)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_PUSH, externalSocketAddress, isServer);
};

void
AddressStringMessageSenderPipe::initializePush(uint32_t entityId, uint32_t serviceId)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_PUSH, 
                        n_Const::c_Constants_Control::strGetInProc_ToMessageHub(), false);
};

void
AddressStringMessageSenderPipe::initializeStream(uint32_t entityId, uint32_t serviceId, const std::string& socketAddress, bool isServer)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_STREAM, socketAddress, isServer);
};

void
AddressStringMessageSenderPipe::initializeZmqSocket(uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType, 
                                                    const std::string& socketAddress, bool isServer)
{
    m_entityId = entityId;
    m_serviceId = serviceId;

    // notes about zero mq send and receive high water mark:
    // - in some cases, only one is relevant and other is ignored
    // - in other cases, both high water marks are relevant
    int32_t zmqhighWaterMark{100000};
    
    uxas::communications::transport::ZeroMqSocketConfiguration
    zmqAddressStringNetworkSendSocket(uxas::communications::transport::NETWORK_NAME::zmqLmcpNetwork(),
                                  socketAddress,
                                  zmqSocketType,
                                  isServer,
                                  false,
                                  zmqhighWaterMark,
                                  zmqhighWaterMark);

    m_transportSender = uxas::stduxas::make_unique<uxas::communications::transport::ZeroMqAddressStringSender>(
            (zmqSocketType == ZMQ_STREAM ? true : false));
    m_transportSender->initialize("", m_entityId, m_serviceId, zmqAddressStringNetworkSendSocket);
};

void
AddressStringMessageSenderPipe::sendAddress(const std::string& address)
{
    m_transportSender->sendAddress(address);
};

}; //namespace communications
}; //namespace uxas

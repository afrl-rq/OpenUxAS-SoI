// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "AddressStringMessageReceiverPipe.h"

#include "ZeroMqSocketConfiguration.h"

#include "stdUniquePtr.h"

#include "Constants/Constants_Control.h"

namespace uxas
{
namespace communications
{

void
AddressStringMessageReceiverPipe::initializePull(uint32_t entityId, uint32_t serviceId)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_PULL, 
                        n_Const::c_Constants_Control::strGetInProc_ToMessageHub(), true);
};

void
AddressStringMessageReceiverPipe::initializeExternalSubscription(uint32_t entityId, uint32_t serviceId, 
                                                                 const std::string& externalSocketAddress, bool isServer)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_SUB, externalSocketAddress, isServer);
};

void
AddressStringMessageReceiverPipe::initializeSubscription(uint32_t entityId, uint32_t serviceId)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_SUB, 
                        n_Const::c_Constants_Control::strGetInProc_FromMessageHub(), false);
};

void
AddressStringMessageReceiverPipe::initializeStream(uint32_t entityId, uint32_t serviceId, 
                                                   const std::string& socketAddress, bool isServer)
{
    initializeZmqSocket(entityId, serviceId, ZMQ_STREAM, socketAddress, isServer);
};

void
AddressStringMessageReceiverPipe::initializeZmqSocket(uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType, 
                                                      const std::string& socketAddress, bool isServer)
{
    m_entityId = entityId;
    m_serviceId = serviceId;

    // notes about zero mq send and receive high water mark:
    // - in some cases, only one is relevant and other is ignored
    // - in other cases, both high water marks are relevant
    int32_t zmqhighWaterMark{100000};

    uxas::communications::transport::ZeroMqSocketConfiguration
    zmqAddressStringNetworkReceiveSocket(uxas::communications::transport::NETWORK_NAME::zmqLmcpNetwork(),
                                         socketAddress,
                                         zmqSocketType,
                                         isServer,
                                         true,
                                         zmqhighWaterMark,
                                         zmqhighWaterMark);

    m_transportReceiver = uxas::stduxas::make_unique<uxas::communications::transport::ZeroMqAddressStringReceiver>(
            (zmqSocketType == ZMQ_STREAM ? true : false));
    m_transportReceiver->initialize(m_entityId, m_serviceId, zmqAddressStringNetworkReceiveSocket);
};

bool
AddressStringMessageReceiverPipe::addSubscriptionAddress(const std::string& address)
{
    return (m_transportReceiver->addSubscriptionAddress(address));
};

bool
AddressStringMessageReceiverPipe::removeSubscriptionAddress(const std::string& address)
{
    return (m_transportReceiver->removeSubscriptionAddress(address));
};

std::unique_ptr<std::string>
AddressStringMessageReceiverPipe::getNextAddress()
{
    return (m_transportReceiver->getNextAddress());
};

}; //namespace communications
}; //namespace uxas

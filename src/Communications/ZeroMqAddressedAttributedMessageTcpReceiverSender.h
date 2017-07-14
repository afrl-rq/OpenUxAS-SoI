// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESSED_ATTRIBUTED_MESSAGE_TCP_RECEIVER_SENDER_H
#define UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESSED_ATTRIBUTED_MESSAGE_TCP_RECEIVER_SENDER_H

#include "ZeroMqReceiverBase.h"

#include "AddressedAttributedMessage.h"

#include "UxAS_SentinelSerialBuffer.h"

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class ZeroMqAddressedAttributedMessageTcpReceiverSender
 * 
 * \par Description:
 * <B><i>ZeroMqAddressedAttributedMessageTcpReceiverSender</i></B> receives 
 * and sends AddressedAttributedMessage data objects via a Zero MQ TCP transport
 * 
 * \par Threading:
 * <B><i>ZeroMqAddressedAttributedMessageTcpReceiverSender</i></B> is not designed for multi-threaded use.  
 * Specifically, the following three methods could be unsafe 
 * for multi-threaded use (detailed analysis and testing not performed):
 * <ul style="padding-left:1em;margin-left:0">
 * <li>addSubscriptionAddress
 * <li>removeSubscriptionAddress
 * <li>getNextMessage
 * </ul>
 * 
 * \n
 */
class ZeroMqAddressedAttributedMessageTcpReceiverSender : public ZeroMqReceiverBase
{

public:
    
    ZeroMqAddressedAttributedMessageTcpReceiverSender()
    : ZeroMqReceiverBase() { };
    
    ~ZeroMqAddressedAttributedMessageTcpReceiverSender() { };

private:

    /** \brief Copy construction not permitted */
    ZeroMqAddressedAttributedMessageTcpReceiverSender(ZeroMqAddressedAttributedMessageTcpReceiverSender const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(ZeroMqAddressedAttributedMessageTcpReceiverSender const&) = delete;

public:

    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
    getNextMessage();
    
    void
    sendMessage(const std::string& address, const std::string& contentType, const std::string& descriptor, const std::string& payload);
    
    void
    sendAddressedAttributedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> message);

private:

    uxas::common::SentinelSerialBuffer m_receiveTcpDataBuffer;
    std::string m_sourceGroup;
    
    // for return sending for zeromq tcp sockets
    size_t m_idSize{0};
    uint8_t m_id[256];

};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESSED_ATTRIBUTED_MESSAGE_TCP_RECEIVER_SENDER_H */


// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESSED_ATTRIBUTED_MESSAGE_SENDER_H
#define UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESSED_ATTRIBUTED_MESSAGE_SENDER_H

#include "ZeroMqSenderBase.h"

#include "AddressedAttributedMessage.h"

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class ZeroMqAddressedAttributedMessageSender
 * 
 * @par Description:
 * Composes and sends single-part or multi-part messages across Zero MQ network.
 */
class ZeroMqAddressedAttributedMessageSender : public ZeroMqSenderBase
{
    
public:
    
    ZeroMqAddressedAttributedMessageSender(bool isTcpStream = false)
    : ZeroMqSenderBase() { m_isTcpStream = isTcpStream; };

    ~ZeroMqAddressedAttributedMessageSender() { };

private:

    /** \brief Copy construction not permitted */
    ZeroMqAddressedAttributedMessageSender(ZeroMqAddressedAttributedMessageSender const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(ZeroMqAddressedAttributedMessageSender const&) = delete;

public:

    void
    sendMessage(const std::string& address, const std::string& contentType, const std::string& descriptor, const std::string payload);
    
    void
    sendAddressedAttributedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> message);

private:

    bool m_isTcpStream{false};
    
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESSED_ATTRIBUTED_MESSAGE_SENDER_H */


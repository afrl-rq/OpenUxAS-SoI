// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESSED_ATTRIBUTED_MESSAGE_RECEIVER_H
#define UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESSED_ATTRIBUTED_MESSAGE_RECEIVER_H

#include <deque>
#include "ZeroMqReceiverBase.h"

#include "AddressedAttributedMessage.h"

#include "UxAS_SentinelSerialBuffer.h"

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class ZeroMqAddressedAttributedMessageReceiver
 * 
 * \par Description:
 * <B><i>ZeroMqAddressedAttributedMessageReceiver</i></B> receives Zero MQ transported messages and 
 * converts them into a AddressedAttributedMessage data object.
 * 
 * \par Threading:
 * <B><i>ZeroMqAddressedAttributedMessageReceiver</i></B> is not designed for multi-threaded use.  
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
class ZeroMqAddressedAttributedMessageReceiver : public ZeroMqReceiverBase
{

public:
    
    ZeroMqAddressedAttributedMessageReceiver(bool isTcpStream = false)
    : ZeroMqReceiverBase(), m_isTcpStream(isTcpStream) { };
    
    ~ZeroMqAddressedAttributedMessageReceiver() { };

private:

    /** \brief Copy construction not permitted */
    ZeroMqAddressedAttributedMessageReceiver(ZeroMqAddressedAttributedMessageReceiver const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(ZeroMqAddressedAttributedMessageReceiver const&) = delete;

public:

    /** \brief Get next AddressedAttributedMessage.
     * 
     * \par Usage example:
     * \code{.cpp}
     * while (true)
     * {In file included from ../../uxas/message/transport/ZeroMqAddressedAttributedMessageReceiver.cpp:1:0:
     *     std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> nextMessage
     *             = m_ZeroMqAddressedAttributedMessageReceiver::getNextMessage();
     *     if (nextMessage)
     *     {
     *         // process received AddressedAttributedMessage object
     *     }
     *     else
     *     {
     *         break; // no more AddressedAttributedMessage objects to receive
     *     }
     * }
     * \endcode
     */
    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
    getNextMessage();
    
private:

    bool m_isTcpStream{false};

    uxas::common::SentinelSerialBuffer m_receiveTcpDataBuffer;
    std::deque< std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> > m_recvdMsgs;

};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESSED_ATTRIBUTED_MESSAGE_RECEIVER_H */


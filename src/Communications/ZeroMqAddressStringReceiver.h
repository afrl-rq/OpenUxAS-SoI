// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESS_STRING_RECEIVER_H
#define	UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESS_STRING_RECEIVER_H

#include "ZeroMqReceiverBase.h"

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class ZeroMqAddressStringReceiver
 * 
 * \par Description:
 * <B><i>ZeroMqAddressStringReceiver</i></B> receives Zero MQ transported messages and 
 * converts them into a AddressedAttributedMessage data object.
 * 
 * \par Threading:
 * <B><i>ZeroMqAddressStringReceiver</i></B> is not designed for multi-threaded use.  
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
class ZeroMqAddressStringReceiver : public ZeroMqReceiverBase
{

public:
    
    ZeroMqAddressStringReceiver(bool isTcpStream = false)
    : ZeroMqReceiverBase() { m_isTcpStream = isTcpStream; };    
    
    ~ZeroMqAddressStringReceiver() { };

private:

    // \brief Prevent copy construction
    ZeroMqAddressStringReceiver(const ZeroMqAddressStringReceiver&) = delete;

    // \brief Prevent copy assignment operation
    ZeroMqAddressStringReceiver& operator=(const ZeroMqAddressStringReceiver&) = delete;

public:

    std::unique_ptr<std::string>
    getNextAddress();

private:

    bool m_isTcpStream{false};
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif	/* UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESS_STRING_RECEIVER_H */


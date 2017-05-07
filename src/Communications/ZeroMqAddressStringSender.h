// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESS_STRING_SENDER_H
#define	UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESS_STRING_SENDER_H

#include "ZeroMqSenderBase.h"

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class ZeroMqAddressStringSender
 * 
 * @par Description:
 * Composes and sends single-part or multi-part messages across Zero MQ network.
 */
class ZeroMqAddressStringSender : public ZeroMqSenderBase
{
    
public:
    
    ZeroMqAddressStringSender(bool isTcpStream = false)
    : ZeroMqSenderBase() { m_isTcpStream = isTcpStream; };

    ~ZeroMqAddressStringSender() { };

private:

    // \brief Prevent copy construction
    ZeroMqAddressStringSender(const ZeroMqAddressStringSender&) = delete;
    
    // \brief Prevent copy assignment operation
    ZeroMqAddressStringSender& operator=(const ZeroMqAddressStringSender&) = delete;

public:

    void
    sendAddress(const std::string& address);

private:

    bool m_isTcpStream{false};

};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif	/* UXAS_MESSAGE_TRANSPORT_ZERO_MQ_ADDRESS_STRING_SENDER_H */


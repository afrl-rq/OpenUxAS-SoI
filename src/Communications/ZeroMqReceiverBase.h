// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_ZERO_MQ_RECEIVER_BASE_H
#define UXAS_MESSAGE_TRANSPORT_ZERO_MQ_RECEIVER_BASE_H

#include "TransportReceiverBase.h"

#include "ZeroMqSocketConfiguration.h"

#include "UxAS_ZeroMQ.h"

#include <memory>

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class ZeroMqReceiverBase
 * 
 * \par Description:
 * <B><i>ZeroMqReceiverBase</i></B> receives Zero MQ transported messages and 
 * converts them into a AddressedAttributedMessage data object.
 * 
 * \par Threading:
 * <B><i>ZeroMqReceiverBase</i></B> is not designed for multi-threaded use.  
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
class ZeroMqReceiverBase : public TransportReceiverBase
{

public:
    
    ZeroMqReceiverBase()
    : TransportReceiverBase() { };

    virtual
    ~ZeroMqReceiverBase();

private:

    /** \brief Copy construction not permitted */
    ZeroMqReceiverBase(ZeroMqReceiverBase const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(ZeroMqReceiverBase const&) = delete;

public:

    void
    initialize(uint32_t entityId, uint32_t serviceId, SocketConfiguration& zeroMqSocketConfiguration);
    
    bool
    addSubscriptionAddressToSocket(const std::string& address) override;

    bool
    removeSubscriptionAddressFromSocket(const std::string& address) override;

protected:

    std::string m_entityIdString;
    std::string m_serviceIdString;

    ZeroMqSocketConfiguration m_zeroMqSocketConfiguration;
    std::unique_ptr<zmq::socket_t> m_zmqSocket;
    
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_ZERO_MQ_RECEIVER_BASE_H */


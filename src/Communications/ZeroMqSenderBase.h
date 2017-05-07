// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_ZERO_MQ_SENDER_BASE_H
#define UXAS_MESSAGE_TRANSPORT_ZERO_MQ_SENDER_BASE_H

#include "TransportBase.h"

#include "ZeroMqSocketConfiguration.h"

#include "UxAS_ZeroMQ.h"

#include <memory>

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class ZeroMqSenderBase
 * 
 * @par Description:
 * Composes and sends messages across Zero MQ network.
 */
class ZeroMqSenderBase : public TransportBase
{
    
public:
    
    ZeroMqSenderBase()
    : TransportBase() { };

    virtual
    ~ZeroMqSenderBase();

private:

    /** \brief Copy construction not permitted */
    ZeroMqSenderBase(ZeroMqSenderBase const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(ZeroMqSenderBase const&) = delete;

public:

    void
    initialize(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId, SocketConfiguration& zeroMqSocketConfiguration);
    
protected:

    std::string m_sourceGroup;
    std::string m_entityIdString;
    std::string m_serviceIdString;
    
    ZeroMqSocketConfiguration m_zeroMqSocketConfiguration;
    std::unique_ptr<zmq::socket_t> m_zmqSocket;

};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_ZERO_MQ_SENDER_BASE_H */


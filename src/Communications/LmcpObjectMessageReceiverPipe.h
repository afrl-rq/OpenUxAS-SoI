// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_MESSAGE_RECEIVER_PIPE_H
#define UXAS_MESSAGE_LMCP_OBJECT_MESSAGE_RECEIVER_PIPE_H

#include "AddressedAttributedMessage.h"
#include "LmcpMessage.h"

#include "ZeroMqAddressedAttributedMessageReceiver.h"

#include "avtas/lmcp/Object.h"

#include <memory>
#include <string>
#include <vector>

namespace uxas
{
namespace communications
{

/** \class LmcpObjectMessageReceiverPipe
 * 
 * \par Description:
 * ... description ...
 * 
 * \n
 */
class LmcpObjectMessageReceiverPipe
{
public:

    LmcpObjectMessageReceiverPipe() { };

    ~LmcpObjectMessageReceiverPipe() { };

private:

    /** \brief Copy construction not permitted */
    LmcpObjectMessageReceiverPipe(LmcpObjectMessageReceiverPipe const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectMessageReceiverPipe const&) = delete;

public:

    void
    initializePull(uint32_t entityId, uint32_t serviceId);
    
    void
    initializeExternalSubscription(uint32_t entityId, uint32_t serviceId, const std::string& externalSocketAddress, bool isServer);

    void
    initializeExternalPull(uint32_t entityId, uint32_t serviceId, const std::string& externalSocketAddress, bool isServer);

    void
    initializeSubscription(uint32_t entityId, uint32_t serviceId);

    void
    initializeStream(uint32_t entityId, uint32_t serviceId, const std::string& socketAddress, bool isServer);

    bool
    addLmcpObjectSubscriptionAddress(const std::string& address);

    bool
    removeLmcpObjectSubscriptionAddress(const std::string& address);
    
    bool
    removeAllLmcpObjectSubscriptionAddresses();
    
    /** \brief Get next LMCP message.
     * 
     * @return <b>LMCP</b> message object.
     */
    std::unique_ptr<uxas::communications::data::LmcpMessage>
    getNextMessageObject();

    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
    getNextSerializedMessage();

    std::unique_ptr<avtas::lmcp::Object>
    deserializeMessage(const std::string& payload);

private:

    void
    initializeZmqSocket(uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType, 
               const std::string& socketAddress, bool isServer);

public:

    uint32_t m_entityId;
    uint32_t m_serviceId;

protected:

    std::unique_ptr<uxas::communications::transport::ZeroMqAddressedAttributedMessageReceiver> m_transportReceiver;

};

}; //namespace communications
}; //namespace uxas


#endif /* UXAS_MESSAGE_LMCP_OBJECT_MESSAGE_RECEIVER_PIPE_H */

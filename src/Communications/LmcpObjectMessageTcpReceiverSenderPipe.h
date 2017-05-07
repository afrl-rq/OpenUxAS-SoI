// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_MESSAGE_TCP_RECEIVER_SENDER_PIPE_H
#define UXAS_MESSAGE_LMCP_OBJECT_MESSAGE_TCP_RECEIVER_SENDER_PIPE_H

#include "AddressedAttributedMessage.h"
#include "LmcpMessage.h"

#include "ZeroMqAddressedAttributedMessageTcpReceiverSender.h"

#include "avtas/lmcp/Object.h"
//#include "transport/ZeroMqAddressedAttributedMessageTcpReceiverSender.h"

#include <memory>
#include <string>
#include <vector>

namespace uxas
{
namespace communications
{

/** \class LmcpObjectMessageTcpReceiverSenderPipe
 * 
 * \par Description:
 * ... description ...
 * 
 * \n
 */
class LmcpObjectMessageTcpReceiverSenderPipe
{
public:

    LmcpObjectMessageTcpReceiverSenderPipe() { };

    ~LmcpObjectMessageTcpReceiverSenderPipe() { };

private:

    /** \brief Copy construction not permitted */
    LmcpObjectMessageTcpReceiverSenderPipe(LmcpObjectMessageTcpReceiverSenderPipe const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectMessageTcpReceiverSenderPipe const&) = delete;

public:

    void
    initializeStream(uint32_t entityId, uint32_t serviceId, const std::string& socketAddress, bool isServer);

    bool
    addLmcpObjectSubscriptionAddress(const std::string& address);

    bool
    removeLmcpObjectSubscriptionAddress(const std::string& address);    
    
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

    void
    sendBroadcastMessage(std::unique_ptr<avtas::lmcp::Object> lmcpObject);

    void
    sendLimitedCastMessage(const std::string& castAddress, std::unique_ptr<avtas::lmcp::Object> lmcpObject);

    void
    sendSerializedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> serializedLmcpObject);

    void
    sendSharedBroadcastMessage(const std::shared_ptr<avtas::lmcp::Object>& lmcpObject);

    void
    sendSharedLimitedCastMessage(const std::string& castAddress, const std::shared_ptr<avtas::lmcp::Object>& lmcpObject);

private:

    void
    initializeZmqSocket(uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType, const std::string& socketAddress, bool isServer);

public:

    uint32_t m_entityId;
    uint32_t m_serviceId;

protected:

    std::unique_ptr<uxas::communications::transport::ZeroMqAddressedAttributedMessageTcpReceiverSender> m_transportTcpReceiverSender;

};

}; //namespace communications
}; //namespace uxas


#endif /* UXAS_MESSAGE_LMCP_OBJECT_MESSAGE_TCP_RECEIVER_SENDER_PIPE_H */

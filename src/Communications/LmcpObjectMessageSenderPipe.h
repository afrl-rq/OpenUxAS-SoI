// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_LMCP_OBJECT_MESSAGE_SENDER_PIPE_H
#define UXAS_MESSAGE_LMCP_OBJECT_MESSAGE_SENDER_PIPE_H

#include "ZeroMqAddressedAttributedMessageSender.h"

#include "avtas/lmcp/Object.h"

#include <memory>
#include <string>

namespace uxas
{
namespace communications
{

/** \class LmcpObjectMessageSenderPipe
 * 
 * \par Description:
 * ... description ...
 * 
 * \n
 */

class LmcpObjectMessageSenderPipe
{
public:

    LmcpObjectMessageSenderPipe() { };

    ~LmcpObjectMessageSenderPipe() { };

private:

    /** \brief Copy construction not permitted */
    LmcpObjectMessageSenderPipe(LmcpObjectMessageSenderPipe const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(LmcpObjectMessageSenderPipe const&) = delete;

public:

    void
    initializePublish(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId);

    void
    initializeExternalPush(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId,
                            const std::string& externalSocketAddress, bool isServer);
    void
    initializeExternalPub(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId,
                          const std::string& externalSocketAddress, bool isServer);
    
    void
    initializePush(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId);

    void
    initializeStream(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId, const std::string& socketAddress, bool isServer);
    
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
    initializeZmqSocket(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType, 
            const std::string& socketAddress, bool isServer);

public:

    uint32_t m_entityId;
    uint32_t m_serviceId;

private:

    std::unique_ptr<uxas::communications::transport::ZeroMqAddressedAttributedMessageSender> m_transportSender;

};

}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_LMCP_OBJECT_MESSAGE_SENDER_PIPE_H */

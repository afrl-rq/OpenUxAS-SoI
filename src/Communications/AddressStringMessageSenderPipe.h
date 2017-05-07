// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_ADDRESS_STRING_MESSAGE_SENDER_PIPE_H
#define	UXAS_MESSAGE_ADDRESS_STRING_MESSAGE_SENDER_PIPE_H

#include "ZeroMqAddressStringSender.h"

#include <memory>
#include <string>

namespace uxas
{
namespace communications
{

/** \class AddressStringMessageSenderPipe
 * 
 * \par Description:
 * ... description ...
 * 
 * \n
 */

class AddressStringMessageSenderPipe
{
    
public:

    AddressStringMessageSenderPipe() { };

    ~AddressStringMessageSenderPipe() { };

private:

    // \brief Prevent copy construction
    AddressStringMessageSenderPipe(const AddressStringMessageSenderPipe&) = delete;

    // \brief Prevent copy assignment operation
    AddressStringMessageSenderPipe& operator=(const AddressStringMessageSenderPipe&) = delete;

public:

    void
    initializePublish(uint32_t entityId, uint32_t serviceId);

    void
    initializeExternalPush(uint32_t entityId, uint32_t serviceId, const std::string& externalSocketAddress, bool isServer);

    void
    initializePush(uint32_t entityId, uint32_t serviceId);

    void
    initializeStream(uint32_t entityId, uint32_t serviceId, const std::string& tcpAddress, bool isServer);

    void
    sendAddress(const std::string& address);

private:
    
    void
    initializeZmqSocket(uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType, 
                        const std::string& socketAddress, bool isServer);
public:

    uint32_t m_entityId;
    uint32_t m_serviceId;

private:

    std::unique_ptr<uxas::communications::transport::ZeroMqAddressStringSender> m_transportSender;

};

}; //namespace communications
}; //namespace uxas

#endif	/* UXAS_MESSAGE_ADDRESS_STRING_MESSAGE_SENDER_PIPE_H */

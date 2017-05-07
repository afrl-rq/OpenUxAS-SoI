// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_ADDRESS_STRING_MESSAGE_RECEIVER_PIPE_H
#define	UXAS_MESSAGE_ADDRESS_STRING_MESSAGE_RECEIVER_PIPE_H

#include "AddressedAttributedMessage.h"

#include "ZeroMqAddressStringReceiver.h"

#include <memory>
#include <string>
#include <vector>

namespace uxas
{
namespace communications
{

/** \class AddressStringMessageReceiverPipe
 * 
 * \par Description:
 * ... description ...
 * 
 * \n
 */
class AddressStringMessageReceiverPipe
{

public:

    AddressStringMessageReceiverPipe() { };

    ~AddressStringMessageReceiverPipe() { };

private:

    // \brief Prevent copy construction
    AddressStringMessageReceiverPipe(const AddressStringMessageReceiverPipe&) = delete;

    // \brief Prevent copy assignment operation
    AddressStringMessageReceiverPipe& operator=(const AddressStringMessageReceiverPipe&) = delete;

public:

    void
    initializePull(uint32_t entityId, uint32_t serviceId);

    void
    initializeExternalSubscription(uint32_t entityId, uint32_t serviceId, const std::string& externalSocketAddress, bool isServer);
    
    void
    initializeSubscription(uint32_t entityId, uint32_t serviceId);

    void
    initializeStream(uint32_t entityId, uint32_t serviceId, const std::string& tcpAddress, bool isServer);

    bool
    addSubscriptionAddress(const std::string& address);

    bool
    removeSubscriptionAddress(const std::string& address);
    
    /** \brief Get next LMCP object.
     * 
     * \par Usage example:
     * \code
     * while (true)
     * {
     *     std::unique_ptr<std::string> receivedLmcpObject = m_AddressStringMessageReceiverPipe::getNextAddress();
     *     if (receivedLmcpObject)
     *     {
     *         // process received LMCP object
     *     }
     *     else
     *     {
     *         break; // no more LMCP objects to receive
     *     }
     * }
     * \endcode
     */
    std::unique_ptr<std::string>
    getNextAddress();

private:

    void
    initializeZmqSocket(uint32_t entityId, uint32_t serviceId, int32_t zmqSocketType, 
                        const std::string& socketAddress, bool isServer);

public:

    uint32_t m_entityId;
    uint32_t m_serviceId;

private:

    std::unique_ptr<uxas::communications::transport::ZeroMqAddressStringReceiver> m_transportReceiver;
    
};

}; //namespace communications
}; //namespace uxas


#endif	/* UXAS_MESSAGE_ADDRESS_STRING_MESSAGE_RECEIVER_PIPE_H */

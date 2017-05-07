// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_TRANSPORT_RECEIVER_BASE_H
#define UXAS_MESSAGE_TRANSPORT_TRANSPORT_RECEIVER_BASE_H

#include "TransportBase.h"

#include <unordered_set>

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class TransportReceiverBase
 * 
 * \par Description:
 * Receives transported messages and converts them into a AddressedAttributedMessage data object.
 * 
 * \n
 */
class TransportReceiverBase : public TransportBase
{
    
public:
    
    TransportReceiverBase()
    : TransportBase() { };

    virtual
    ~TransportReceiverBase() { };

private:

    /** \brief Copy construction not permitted */
    TransportReceiverBase(TransportReceiverBase const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(TransportReceiverBase const&) = delete;

public:    
    
    bool
    addSubscriptionAddress(const std::string& address);

    bool
    removeSubscriptionAddress(const std::string& address);

    bool
    removeAllSubscriptionAddresses();

protected:    
    
    virtual
    bool
    addSubscriptionAddressToSocket(const std::string& address) { return false; };

    virtual
    bool
    removeSubscriptionAddressFromSocket(const std::string& address) { return false; };

private:
    
    std::unordered_set<std::string> m_subscriptionAddresses;

};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_TRANSPORT_RECEIVER_BASE_H */

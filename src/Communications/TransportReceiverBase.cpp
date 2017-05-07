// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "TransportReceiverBase.h"

namespace uxas
{
namespace communications
{
namespace transport
{

bool
TransportReceiverBase::addSubscriptionAddress(const std::string& address)
{
    bool isAdded(false);
    auto addressCheck = m_subscriptionAddresses.find(address);
    if (addressCheck == m_subscriptionAddresses.end())
    {
        m_subscriptionAddresses.emplace(address);
        isAdded = addSubscriptionAddressToSocket(address);
    }
    return (isAdded);
};

bool
TransportReceiverBase::removeSubscriptionAddress(const std::string& address)
{
    bool isRemoved(false);
    auto addressCheck = m_subscriptionAddresses.find(address);
    if (addressCheck != m_subscriptionAddresses.end())
    {
        m_subscriptionAddresses.erase(addressCheck);
        isRemoved = removeSubscriptionAddressFromSocket(address);
    }
    return (isRemoved);
};

bool
TransportReceiverBase::removeAllSubscriptionAddresses()
{
    for (auto addressIt = m_subscriptionAddresses.begin(); addressIt != m_subscriptionAddresses.end();)
    {
        removeSubscriptionAddressFromSocket(*addressIt);
    }
    if (m_subscriptionAddresses.size() < 1)
    {
        return (true);
    }
    return (false);
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

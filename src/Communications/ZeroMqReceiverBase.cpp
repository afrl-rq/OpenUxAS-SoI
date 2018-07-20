// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ZeroMqReceiverBase.h"

#include "ZeroMqFabric.h"
#include "UxAS_Log.h"

#include <chrono>
#include <thread>

namespace uxas
{
namespace communications
{
namespace transport
{

ZeroMqReceiverBase::~ZeroMqReceiverBase()
{
//    UXAS_LOG_INFORM_ASSIGNMENT("~ZeroMqReceiverBase() -Begin");
    uint32_t lingerDuration_ms(0);
    if (m_zmqSocket)
    {
        m_zmqSocket->setsockopt(ZMQ_LINGER, &lingerDuration_ms, sizeof(lingerDuration_ms));
        std::this_thread::sleep_for(std::chrono::milliseconds(10));
        m_zmqSocket->close();
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        m_zmqSocket.reset();
    }

//    UXAS_LOG_INFORM_ASSIGNMENT("~ZeroMqReceiverBase()- End");
};

void
ZeroMqReceiverBase::initialize(uint32_t entityId, uint32_t serviceId, SocketConfiguration& zeroMqSocketConfiguration)
{
    m_entityId = entityId;
    m_serviceId = serviceId;
    m_entityIdString = std::to_string(entityId);
    m_serviceIdString = std::to_string(serviceId);

    m_zeroMqSocketConfiguration = static_cast<ZeroMqSocketConfiguration&> (zeroMqSocketConfiguration);
    try
    {
        m_zmqSocket = ZeroMqFabric::getInstance().createSocket(m_zeroMqSocketConfiguration);
    }
    catch (std::exception& ex)
    {
        UXAS_LOG_ERROR("ZeroMqReceiverBase::initialize, create socket EXCEPTION: ", ex.what());
        m_zmqSocket = nullptr;
    }
};

bool
ZeroMqReceiverBase::addSubscriptionAddressToSocket(const std::string& address)
{
    bool isAdded(false);
    if (m_zeroMqSocketConfiguration.m_zmqSocketType == ZMQ_SUB)
    {
        m_zmqSocket->setsockopt(ZMQ_SUBSCRIBE, address.c_str(), address.size());
        isAdded = true;
    }
    return (isAdded);
};

bool
ZeroMqReceiverBase::removeSubscriptionAddressFromSocket(const std::string& address)
{
    bool isRemoved(false);
    if (m_zeroMqSocketConfiguration.m_zmqSocketType == ZMQ_SUB)
    {
        m_zmqSocket->setsockopt(ZMQ_UNSUBSCRIBE, address.c_str(), address.size());
        isRemoved = true;
    }
    return (isRemoved);
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

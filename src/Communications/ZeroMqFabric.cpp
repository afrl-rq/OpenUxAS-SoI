// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ZeroMqFabric.h"

#include "stdUniquePtr.h"
#include "UxAS_Log.h"

#include <chrono>
#include <thread>

namespace uxas
{
namespace communications
{
namespace transport
{

std::unique_ptr<ZeroMqFabric> ZeroMqFabric::s_instance = nullptr;

ZeroMqFabric&
ZeroMqFabric::getInstance()
{
    // first time/one time creation
    if (!ZeroMqFabric::s_instance)
    {
        s_instance.reset(new ZeroMqFabric);
        s_instance->m_zmqContext = uxas::stduxas::make_unique<zmq::context_t>(1);
    }

    return *s_instance;
};

void ZeroMqFabric::Destroy()
{
    s_instance.reset(nullptr);
}

ZeroMqFabric::~ZeroMqFabric()
{
    if(m_zmqContext)
    {
        LOG_INFORM_ASSIGNMENT("****** ZeroMqFabric::~ZeroMqFabric() - Starting to shut down m_zmqContext !!! ******");
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        m_zmqContext->close();
        zmq_ctx_destroy(m_zmqContext.get());
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        m_zmqContext.reset();
    }
    LOG_INFORM_ASSIGNMENT("****** ZeroMqFabric::~ZeroMqFabric() - Finished shutting down m_zmqContext !!! ******");
};

std::unique_ptr<zmq::socket_t>
ZeroMqFabric::createSocket(ZeroMqSocketConfiguration& socketConfiguration)
{
    std::unique_ptr<zmq::socket_t> zmqSocket = uxas::stduxas::make_unique<zmq::socket_t>(*m_zmqContext, socketConfiguration.m_zmqSocketType);
    if (socketConfiguration.m_isServerBind)
    {
        zmqSocket->bind(socketConfiguration.m_socketAddress.c_str());
    }
    else
    {
        zmqSocket->connect(socketConfiguration.m_socketAddress.c_str());
    }
    zmqSocket->setsockopt(ZMQ_RCVHWM, &socketConfiguration.m_receiveHighWaterMark, sizeof (socketConfiguration.m_receiveHighWaterMark));
    zmqSocket->setsockopt(ZMQ_SNDHWM, &socketConfiguration.m_sendHighWaterMark, sizeof (socketConfiguration.m_sendHighWaterMark));
    return (zmqSocket);
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

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
        UXAS_LOG_INFORM_ASSIGNMENT("****** ZeroMqFabric::~ZeroMqFabric() - Starting to shut down m_zmqContext !!! ******");
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        m_zmqContext->close();
        zmq_ctx_destroy(m_zmqContext.get());
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        m_zmqContext.reset();
    }
    UXAS_LOG_INFORM_ASSIGNMENT("****** ZeroMqFabric::~ZeroMqFabric() - Finished shutting down m_zmqContext !!! ******");
};

std::unique_ptr<zmq::socket_t>
ZeroMqFabric::createSocket(ZeroMqSocketConfiguration& socketConfiguration)
{
    UXAS_LOG_DEBUGGING("ZeroMqFabric::createSocket method START");
    if(!m_zmqContext)
    {
        UXAS_LOG_ERROR("ZeroMqFabric::createSocket ZMQ context has not been created");
        return std::unique_ptr<zmq::socket_t>(nullptr);
    }
    
    UXAS_LOG_DEBUGGING("ZeroMqFabric::createSocket attempting to build socket of type ", socketConfiguration.m_zmqSocketType);
    std::unique_ptr<zmq::socket_t> zmqSocket = uxas::stduxas::make_unique<zmq::socket_t>(*m_zmqContext, socketConfiguration.m_zmqSocketType);
    
    if(!zmqSocket)
    {
        UXAS_LOG_ERROR("ZeroMqFabric::createSocket ZMQ socket could not be created with type ", socketConfiguration.m_zmqSocketType);
        return std::unique_ptr<zmq::socket_t>(nullptr);
    }
    
    UXAS_LOG_DEBUGGING("ZeroMqFabric::createSocket new ZMQ socket successfully created with type ", socketConfiguration.m_zmqSocketType);
    if (socketConfiguration.m_isServerBind)
    {
        UXAS_LOG_DEBUGGING("ZeroMqFabric::createSocket BINDING socket to ", socketConfiguration.m_socketAddress.c_str());
        zmqSocket->bind(socketConfiguration.m_socketAddress.c_str());
    }
    else
    {
        UXAS_LOG_DEBUGGING("ZeroMqFabric::createSocket CONNECTING socket to ", socketConfiguration.m_socketAddress.c_str());
        zmqSocket->connect(socketConfiguration.m_socketAddress.c_str());
    }
    UXAS_LOG_DEBUGGING("ZeroMqFabric::createSocket setting RCV high-water mark for socket to ", socketConfiguration.m_receiveHighWaterMark);
    zmqSocket->setsockopt(ZMQ_RCVHWM, &socketConfiguration.m_receiveHighWaterMark, sizeof (socketConfiguration.m_receiveHighWaterMark));
    UXAS_LOG_DEBUGGING("ZeroMqFabric::createSocket setting SEND high-water mark for socket to ", socketConfiguration.m_sendHighWaterMark);
    zmqSocket->setsockopt(ZMQ_SNDHWM, &socketConfiguration.m_sendHighWaterMark, sizeof (socketConfiguration.m_sendHighWaterMark));
    UXAS_LOG_DEBUGGING("ZeroMqFabric::createSocket method END");
    return (zmqSocket);
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

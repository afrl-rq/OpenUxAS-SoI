// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_ZERO_MQ_FABRIC_H
#define UXAS_MESSAGE_TRANSPORT_ZERO_MQ_FABRIC_H

#include "ZeroMqSocketConfiguration.h"

#include "UxAS_ZeroMQ.h"

#include <memory>

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class ZeroMqFabric
 * 
 * \par Description:
 * Singleton pattern
 * 
 * \n
 */
class ZeroMqFabric final
{
    
public:

    static ZeroMqFabric& getInstance();
    static void Destroy();
    ~ZeroMqFabric();

    std::unique_ptr<zmq::socket_t>
    createSocket(ZeroMqSocketConfiguration& socketConfiguration);

private:

    /** \brief Public, direct construction not permitted (singleton pattern) */
    ZeroMqFabric() { };

    /** \brief Copy construction not permitted */
    ZeroMqFabric(ZeroMqFabric const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(ZeroMqFabric const&) = delete;

    static std::unique_ptr<ZeroMqFabric> s_instance;

    std::unique_ptr<zmq::context_t> m_zmqContext;

};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_ZERO_MQ_FABRIC_H */

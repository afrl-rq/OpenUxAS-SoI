// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_ZERO_MQ_SOCKET_CONFIGURATION_H
#define UXAS_MESSAGE_TRANSPORT_ZERO_MQ_SOCKET_CONFIGURATION_H

#include <cstdint>
#include "SocketConfiguration.h"

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class ZeroMqSocketConfiguration
 * 
 * \par Description:
 * Zero MQ transport socket configuration data object.
 * 
 * \n
 */
class ZeroMqSocketConfiguration : public SocketConfiguration
{

public:

    ZeroMqSocketConfiguration()
    : SocketConfiguration() { };

    ZeroMqSocketConfiguration(const std::string& networkName, const std::string& socketAddress,
                              const int32_t zmqSocketType, const bool isServerBind, const bool isReceive,
                              const int32_t receiveHighWaterMark, const int32_t sendHighWaterMark)
    : SocketConfiguration(networkName, socketAddress, isReceive),
    m_zmqSocketType(zmqSocketType), m_isServerBind(isServerBind),
    m_receiveHighWaterMark(receiveHighWaterMark), m_sendHighWaterMark(sendHighWaterMark) { };

    int32_t m_zmqSocketType;
    bool m_isServerBind{false};
    int32_t m_receiveHighWaterMark{0};
    int32_t m_sendHighWaterMark{0};

};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_ZERO_MQ_SOCKET_CONFIGURATION_H */


// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_SOCKET_CONFIGURATION_H
#define UXAS_MESSAGE_TRANSPORT_SOCKET_CONFIGURATION_H

#include <string>

namespace uxas
{
namespace communications
{
namespace transport
{

/** \class SocketConfiguration
 * 
 * \par Description:
 * Basic transport socket configuration data object.
 * 
 * \n
 */
class SocketConfiguration
{

public:

    SocketConfiguration() { };
    
    SocketConfiguration(const std::string& networkName, const std::string& socketAddress, const bool isReceive)
    : m_networkName(networkName), m_socketAddress(socketAddress), m_isReceive(isReceive) { };

    std::string m_networkName;
    std::string m_socketAddress;
    bool m_isReceive;

};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_SOCKET_CONFIGURATION_H */


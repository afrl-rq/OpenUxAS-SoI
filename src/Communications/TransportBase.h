// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_TRANSPORT_TRANSPORT_BASE_H
#define UXAS_MESSAGE_TRANSPORT_TRANSPORT_BASE_H

#include "SocketConfiguration.h"

#include <string>
#include <cstdint>

namespace uxas
{
namespace communications
{
namespace transport
{

class NETWORK_NAME
{
public:
    static const std::string& zmqExternalLmcpTcpNetwork(){static std::string strString("zmqExternalLmcpTcpNetwork");return(strString);};
    static const std::string& zmqLmcpNetwork(){static std::string strString("zmqLmcpNetwork");return(strString);};
    static const std::string& zmqStringNetwork(){static std::string strString("zmqStringNetwork");return(strString);};
};

/** \class TransportBase
 * 
 * \par Description:     
 * <B><i>CLASSNAME</i></B> ...
 * 
 * <ul style="padding-left:1em;margin-left:0">
 * <li>Initialization
 * <li>Configuration
 * <li>Thread management
 * <li>Message management
 * </ul>
 * 
 * \par Highlights:
 * <ul style="padding-left:1em;margin-left:0">
 * <li> Initialization -
 * CLASSNAME initialization is ...
 * 
 * <li> Configuration -
 * CLASSNAME configuration is ...
 * 
 * <li> Thread Management -
 * CLASSNAME thread management is ...
 * 
 * <li> Messaging -
 * CLASSNAME messaging is ...
 * </ul>
 * ../../uxas/message/LmcpObjectMessageSender.h:65:21: error: ‘StringMessageSenderBase’ is not a member of ‘uxas::communications::transport’
 * \par Configuration:
 * 
 * \n
 */

class TransportBase
{

public:

    TransportBase() { };

    virtual
    ~TransportBase() { };

private:

    /** \brief Copy construction not permitted */
    TransportBase(TransportBase const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(TransportBase const&) = delete;

public:

    uint32_t m_entityId;
    uint32_t m_serviceId;

};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_TRANSPORT_TRANSPORT_BASE_H */


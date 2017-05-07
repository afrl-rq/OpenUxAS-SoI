// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ZeroMqAddressStringSender.h"

#include "UxAS_ZeroMQ.h"

namespace uxas
{
namespace communications
{
namespace transport
{

void
ZeroMqAddressStringSender::sendAddress(const std::string& address)
{
    if (m_zmqSocket)
    {
        if (m_isTcpStream)
        {
            zmq_send(*m_zmqSocket, address.c_str(), address.size(), ZMQ_SNDMORE);
        }
        else
        {
            n_ZMQ::s_send(*m_zmqSocket, address);
        }
    } //if(m_zmqSocket)
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

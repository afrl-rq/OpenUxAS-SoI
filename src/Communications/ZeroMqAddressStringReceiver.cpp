// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ZeroMqAddressStringReceiver.h"

#include "UxAS_ConfigurationManager.h"

#include "stdUniquePtr.h"

#include "UxAS_ZeroMQ.h"

#include "czmq.h"

namespace uxas
{
namespace communications
{
namespace transport
{

std::unique_ptr<std::string>
ZeroMqAddressStringReceiver::getNextAddress()
{
    std::unique_ptr<std::string> address;
    if (m_zmqSocket)
    {
        zmq::pollitem_t pollItems [] = {
            { *m_zmqSocket, 0, ZMQ_POLLIN, 0},
        };

        zmq::poll(&pollItems[0], 1, uxas::common::ConfigurationManager::getZeroMqReceiveSocketPollWaitTime_ms()); // wait time units are milliseconds
        if (pollItems[0].revents & ZMQ_POLLIN)
        {
            if (m_isTcpStream)
            {
                zframe_t* frameData = zframe_recv(*m_zmqSocket);
                byte* payloadData = zframe_data(frameData);
                size_t payloadSize = zframe_size(frameData);

                std::string framePayload(reinterpret_cast<const char*> (payloadData), payloadSize);
                address = uxas::stduxas::make_unique<std::string>(std::move(framePayload));

                zframe_destroy(&frameData);
            }
            else
            {
                address = uxas::stduxas::make_unique<std::string>(n_ZMQ::s_recv(*m_zmqSocket));
            }
        }
    } //if(m_zmqSocket)

    return (address);
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ZeroMqAddressedAttributedMessageTcpReceiverSender.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Time.h"

#include "stdUniquePtr.h"
#include "UxAS_ZeroMQ.h"

namespace uxas
{
namespace communications
{
namespace transport
{

ZeroMqAddressedAttributedMessageTcpReceiverSender::~ZeroMqAddressedAttributedMessageTcpReceiverSender()
{
    for(auto c : m_clients)
        zframe_destroy(&c);
    m_clients.clear();
}

std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage()
{
    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> nextMsg;
    
    // just send the next message if one is available
    if(!m_recvdMsgs.empty())
    {
        nextMsg = std::move(m_recvdMsgs[0]);
        m_recvdMsgs.pop_front();
        return nextMsg;
    }
    
    // if the socket was not created, exit
    if (!m_zmqSocket)
    {
        UXAS_LOG_ERROR("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage socket not initialized");
        return nextMsg; // blank
    }

    // using the ZMQ_STREAM socket for TCP communications
    // if this socket is not configured properly, exit
    if (m_zeroMqSocketConfiguration.m_zmqSocketType != ZMQ_STREAM)
    {
        UXAS_LOG_ERROR("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage only ZMQ_STREAM socket allowed, but configured as ", m_zeroMqSocketConfiguration.m_zmqSocketType );
        return nextMsg; // blank
    }

    UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE zmq::pollitem_t");
    zmq::pollitem_t pollItems [] = {
        { *m_zmqSocket, 0, ZMQ_POLLIN, 0},
    };
    UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage AFTER zmq::pollitem_t");

    // http://api.zeromq.org/2-1:zmq-poll
    // If none of the requested events have occurred on any zmq_pollitem_t item,
    // zmq_poll() shall wait timeout microseconds for an event to occur on any of
    // the requested items. If the value of timeout is 0, zmq_poll() shall return
    // immediately. If the value of timeout is -1, zmq_poll() shall block
    // indefinitely until a requested event has occurred on at least one
    // zmq_pollitem_t. The resolution of timeout is 1 millisecond.
    zmq::poll(&pollItems[0], 1, uxas::common::ConfigurationManager::getZeroMqReceiveSocketPollWaitTime_ms()); // wait time units are milliseconds
    if (pollItems[0].revents & ZMQ_POLLIN)
    {
        try
        {
            std::lock_guard<std::mutex> lock(m_data_guard);
            
            // ZMQ_STREAM sockets always return two frames, the first identifying the sender
            // (see http://api.zeromq.org/4-1:zmq-socket)

            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE identity frame recv");
            zframe_t* identityFrame = zframe_recv(*m_zmqSocket);
            if(!identityFrame)
            {
                UXAS_LOG_ERROR("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage identity frame read error (null)");
                return nextMsg; // blank
            }
            if(!zframe_more(identityFrame))
            {
                UXAS_LOG_ERROR("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage identity frame requires follow-on payload frame");
                zframe_destroy(&identityFrame);
                return nextMsg; // blank
            }

            // single-part AddressedAttributedMessage in next frame
            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE TCP zframe_recv");
            zframe_t* frameData = zframe_recv(*m_zmqSocket);
            if(!frameData)
            {
                UXAS_LOG_ERROR("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage data frame read error (null)");
                zframe_destroy(&identityFrame); // identity frame was okay, but need to delete before exit
                return nextMsg; // blank
            }

            // extract data and datasize from data frame
            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE TCP zframe_data");
            byte* payloadData = zframe_data(frameData);
            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE TCP zframe_size");
            size_t payloadSize = zframe_size(frameData);

            // if the datasize is zero, then according to (http://api.zeromq.org/4-1:zmq-socket), this is a client connect/disconnect
            if(0 == payloadSize)
            {
                UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage zero-length data frame indicating client connect/disconnect");

                // if the identityFrame is already in the client list, assume this is a disconnect and remove from client list
                size_t clientindex = 0;
                bool alreadyconnected = false;
                for(size_t k=0; k<m_clients.size(); k++)
                {
                    if(zframe_eq(m_clients.at(k),identityFrame))
                    {
                        alreadyconnected = true;
                        clientindex = k;
                        break;
                    }
                }

                if(alreadyconnected)
                {
                    UXAS_LOG_INFORM("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage detecting client disconnect");
                    zframe_destroy(&identityFrame);
                    // don't process potential disconnects: likely very few
                    // clients in general and not worth tracking spurious
                    // disconnects due to reception of a zero length message
                    // disconnect logic is below if desired
                    /*  auto clientdisconnect = m_clients.at(clientindex);
                        m_clients.erase(m_clients.begin()+clientindex);
                        zframe_destroy(&clientdisconnect); */
                }
                else
                {
                    UXAS_LOG_INFORM("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage detecting new client connect");
                    // save identity frame as new client
                    m_clients.push_back(identityFrame);
                }

                zframe_destroy(&frameData); // delete empty frame data
                return nextMsg; // blank
            }

            // at this point we have an actual data frame ready for processing
            // if for some reason, the identity of this actual data is not in the client list, add it
            bool existingclient = false;
            for(auto c : m_clients)
            {
                if(zframe_eq(c,identityFrame))
                {
                    existingclient = true;
                    break;
                }
            }

            if(!existingclient)
            {
                UXAS_LOG_INFORM("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage got a non-zero data packet from unknown client");
                m_clients.push_back(identityFrame);
            }
            else
                zframe_destroy(&identityFrame);


            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE TCP framePayload");
            std::string framePayload(reinterpret_cast<const char*> (payloadData), payloadSize);
            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage TCP framePayload is: [", framePayload, "]");
            std::string recvdTcpDataSegment = m_receiveTcpDataBuffer.getNextPayloadString(framePayload);
            while (!recvdTcpDataSegment.empty())
            {
                UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage processing complete object string segment");
                std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> recvdTcpAddAttMsg
                        = uxas::stduxas::make_unique<uxas::communications::data::AddressedAttributedMessage>();
                if (recvdTcpAddAttMsg->setAddressAttributesAndPayloadFromDelimitedString(std::move(recvdTcpDataSegment)))
                {
                    m_recvdMsgs.push_back( std::move(recvdTcpAddAttMsg) );
                }
                else
                {
                    UXAS_LOG_WARN("ZeroMqAddressedAttributedMessageReceiver::getNextMessage failed to create AddressedAttributedMessage object from TCP stream serial buffer string segment");
                }
                recvdTcpDataSegment = m_receiveTcpDataBuffer.getNextPayloadString("");
            }
            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE zframe_destroy");
            zframe_destroy(&frameData);
        }
        catch (std::exception& ex)
        {
            UXAS_LOG_ERROR("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage EXCEPTION: ", ex.what());
        }
    }

    if(!m_recvdMsgs.empty())
    {
        nextMsg = std::move(m_recvdMsgs[0]);
        m_recvdMsgs.pop_front();
    }
    return nextMsg; // blank if none received
};

void
ZeroMqAddressedAttributedMessageTcpReceiverSender::sendMessage(const std::string& address, const std::string& contentType, const std::string& descriptor, const std::string& payload)
{
    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> message
            = uxas::stduxas::make_unique<uxas::communications::data::AddressedAttributedMessage>();
    message->setAddressAttributesAndPayload(address, contentType, descriptor, m_sourceGroup,
                                           m_entityIdString, m_serviceIdString, std::move(payload));
    sendAddressedAttributedMessage(std::move(message));
};

void
ZeroMqAddressedAttributedMessageTcpReceiverSender::sendAddressedAttributedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> message)
{
    static uint8_t serverid[256];
    static size_t serveridsize{256};

    std::lock_guard<std::mutex> lock(m_data_guard);
    if (m_zmqSocket)
    {
        std::string sentinelStr = uxas::common::SentinelSerialBuffer::createSentinelizedString(message->getString());

        if(m_zeroMqSocketConfiguration.m_isServerBind)
        {
            // send to every connected client
            for(auto c : m_clients)
            {
                // first part of message must be client identity
                zmq_send(*m_zmqSocket, zframe_data(c), zframe_size(c), ZMQ_SNDMORE);
                UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::sendAddressedAttributedMessage BEFORE sending TCP stream single-part message");
                zmq_send(*m_zmqSocket, sentinelStr.c_str(), sentinelStr.size(), 0);
                UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::sendAddressedAttributedMessage AFTER sending TCP stream single-part message");
            }
        }
        else
        {
            // force identity to server id according to http://api.zeromq.org/4-1:zmq-socket
            memset(serverid, 0, 256);
            m_zmqSocket->getsockopt(ZMQ_IDENTITY, serverid, &serveridsize);

            zmq_send(*m_zmqSocket, serverid, serveridsize, ZMQ_SNDMORE);
            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::sendAddressedAttributedMessage BEFORE sending TCP stream single-part message");
            zmq_send(*m_zmqSocket, sentinelStr.c_str(), sentinelStr.size(), 0);
            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::sendAddressedAttributedMessage AFTER sending TCP stream single-part message");
        }
    }
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

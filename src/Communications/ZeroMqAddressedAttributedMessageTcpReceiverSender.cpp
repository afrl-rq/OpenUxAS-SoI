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

#include "czmq.h"

namespace uxas
{
namespace communications
{
namespace transport
{

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
    
    // no messages in queue, attempt to read from TCP socket
    if (m_zmqSocket)
    {
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
                while (true)
                {
                    // single-part AddressedAttributedMessage)
                    UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE TCP zframe_recv");
                    zframe_t* frameData = zframe_recv(*m_zmqSocket);
                    UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE TCP zframe_data");
                    byte* payloadData = zframe_data(frameData);
                    UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage BEFORE TCP zframe_size");
                    size_t payloadSize = zframe_size(frameData);

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
                    if (!m_recvdMsgs.empty() || uxas::common::ConfigurationManager::getZeroMqReceiveSocketPollWaitTime_ms() > -1)
                    {
                        break;
                    }
                }
            }
            catch (std::exception& ex)
            {
                UXAS_LOG_ERROR("ZeroMqAddressedAttributedMessageTcpReceiverSender::getNextMessage EXCEPTION: ", ex.what());
            }
        }
    } //if(m_zmqSocket)

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
    if (m_zmqSocket)
    {
        uxas::communications::data::AddressedAttributedMessage message;
        message.setAddressAttributesAndPayload(address, contentType, descriptor, m_sourceGroup,
                                               m_entityIdString, m_serviceIdString, std::move(payload));
        std::string sentinelStr = uxas::common::SentinelSerialBuffer::createSentinelizedString(message.getString());
        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::sendMessage BEFORE sending TCP stream single-part message");
        zmq_send(*m_zmqSocket, sentinelStr.c_str(), sentinelStr.size(), ZMQ_SNDMORE);
        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::sendMessage AFTER sending TCP stream single-part message");
    } //if(m_zmqSocket)
};

void
ZeroMqAddressedAttributedMessageTcpReceiverSender::sendAddressedAttributedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> message)
{
    if (m_zmqSocket)
    {
        if (m_idSize == 0)
        {
            memset(m_id, 0, 256);
            m_idSize = 256;
            m_zmqSocket->getsockopt(ZMQ_IDENTITY, m_id, &m_idSize);
        }
        zmq_send(*m_zmqSocket, m_id, m_idSize, ZMQ_SNDMORE);

        std::string sentinelStr = uxas::common::SentinelSerialBuffer::createSentinelizedString(message->getString());
        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::sendAddressedAttributedMessage BEFORE sending TCP stream single-part message");
        zmq_send(*m_zmqSocket, sentinelStr.c_str(), sentinelStr.size(), ZMQ_SNDMORE);
        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageTcpReceiverSender::sendAddressedAttributedMessage AFTER sending TCP stream single-part message");
    }
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

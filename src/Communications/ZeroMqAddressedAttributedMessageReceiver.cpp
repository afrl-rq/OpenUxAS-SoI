// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ZeroMqAddressedAttributedMessageReceiver.h"

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
ZeroMqAddressedAttributedMessageReceiver::getNextMessage()
{
    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> nextMsg;

    // just send the next message if one is available
    if(!m_recvdMsgs.empty())
    {
        nextMsg = std::move(m_recvdMsgs[0]);
        m_recvdMsgs.pop_front();
        return nextMsg;
    }
    
    // no messages in queue, attempt to read from socket
    if (m_zmqSocket)
    {
        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage BEFORE zmq::pollitem_t");
        zmq::pollitem_t pollItems [] = {
            { *m_zmqSocket, 0, ZMQ_POLLIN, 0},
        };
        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage AFTER zmq::pollitem_t");

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
            if (m_isTcpStream) // only used for bridging to other entities
            {
                try
                {
                    while (true)
                    {
                        // single-part AddressedAttributedMessage)
                        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage BEFORE TCP zframe_recv");
                        zframe_t* frameData = zframe_recv(*m_zmqSocket);
                        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage BEFORE TCP zframe_data");
                        byte* payloadData = zframe_data(frameData);
                        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage BEFORE TCP zframe_size");
                        size_t payloadSize = zframe_size(frameData);

                        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage BEFORE TCP framePayload");
                        std::string framePayload(reinterpret_cast<const char*> (payloadData), payloadSize);
                        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage TCP framePayload is: [", framePayload, "]");
                        std::string recvdTcpDataSegment = m_receiveTcpDataBuffer.getNextPayloadString(framePayload);
                        while (!recvdTcpDataSegment.empty())
                        {
                            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage processing complete object string segment");
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
                        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage BEFORE zframe_destroy");
                        zframe_destroy(&frameData);
                        if (nextMsg || uxas::common::ConfigurationManager::getZeroMqReceiveSocketPollWaitTime_ms() > -1)
                        {
                            break;
                        }
                    }
                }
                catch (std::exception& ex)
                {
                    UXAS_LOG_ERROR("ZeroMqAddressedAttributedMessageReceiver::getNextMessage EXCEPTION: ", ex.what());
                }
            }
            else
            {
                // not a stream, so should only be a single message
                if (uxas::common::ConfigurationManager::getIsZeroMqMultipartMessage())
                {
                    std::string address = n_ZMQ::s_recv(*m_zmqSocket);
                    std::string contentType = n_ZMQ::s_recv(*m_zmqSocket);
                    std::string descriptor = n_ZMQ::s_recv(*m_zmqSocket);
                    std::string sourceGroup = n_ZMQ::s_recv(*m_zmqSocket);
                    std::string sourceEntityId = n_ZMQ::s_recv(*m_zmqSocket);
                    std::string sourceServiceId = n_ZMQ::s_recv(*m_zmqSocket);
                    std::string payload = n_ZMQ::s_recv(*m_zmqSocket);
                    if (m_entityIdString != sourceEntityId || m_serviceIdString != sourceServiceId)
                    {
                        std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> recvdMultipartAddAttMsg
                                = uxas::stduxas::make_unique<uxas::communications::data::AddressedAttributedMessage>();
                        if (recvdMultipartAddAttMsg->setAddressAttributesAndPayload(std::move(address), std::move(contentType), std::move(descriptor), std::move(sourceGroup),
                                                                                    std::move(sourceEntityId), std::move(sourceServiceId), std::move(payload)))
                        {
                            m_recvdMsgs.push_back( std::move(recvdMultipartAddAttMsg) );
                        }
                        else
                        {
                            UXAS_LOG_WARN("ZeroMqAddressedAttributedMessageReceiver::getNextMessage failed to create AddressedAttributedMessage object from Zero MQ multi-part message");
                        }
                    }
                    else
                    {
                        UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage ignoring ", descriptor, " message with entity ID ", m_entityIdString, " and service ID ", m_serviceIdString, " since it matches its own entity ID");
                    }
                }
                else
                {
                    std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> recvdSinglepartAddAttMsg
                            = uxas::stduxas::make_unique<uxas::communications::data::AddressedAttributedMessage>();
                    if (recvdSinglepartAddAttMsg->setAddressAttributesAndPayloadFromDelimitedString(n_ZMQ::s_recv(*m_zmqSocket)))
                    {
                        if (m_entityIdString != recvdSinglepartAddAttMsg->getMessageAttributesReference()->getSourceEntityId()
                                || m_serviceIdString != recvdSinglepartAddAttMsg->getMessageAttributesReference()->getSourceServiceId())
                        {
                            m_recvdMsgs.push_back( std::move(recvdSinglepartAddAttMsg) );
                        }
                        else
                        {
                            UXAS_LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageReceiver::getNextMessage ignoring ", recvdSinglepartAddAttMsg->getMessageAttributesReference()->getDescriptor(), " message with entity ID ", m_entityIdString, " and service ID ", m_serviceIdString, " since it matches its own entity ID");
                        }
                    }
                    else
                    {
                        UXAS_LOG_WARN("ZeroMqAddressedAttributedMessageReceiver::getNextMessage failed to create AddressedAttributedMessage object from Zero MQ single-part message");
                    }
                }
            }
        }
    } //if(m_zmqSocket)

    if(!m_recvdMsgs.empty())
    {
        nextMsg = std::move(m_recvdMsgs[0]);
        m_recvdMsgs.pop_front();
    }
    return (nextMsg);
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

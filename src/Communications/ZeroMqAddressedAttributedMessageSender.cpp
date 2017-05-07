// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ZeroMqAddressedAttributedMessageSender.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"
#include "UxAS_SentinelSerialBuffer.h"

#include "UxAS_ZeroMQ.h"

namespace uxas
{
namespace communications
{
namespace transport
{

void
ZeroMqAddressedAttributedMessageSender::sendMessage(const std::string& address, const std::string& contentType, const std::string& descriptor, const std::string payload)
{
    if (m_zmqSocket)
    {
        uxas::communications::data::AddressedAttributedMessage message;
        message.setAddressAttributesAndPayload(address, contentType, descriptor, m_sourceGroup,
                                               m_entityIdString, m_serviceIdString, std::move(payload));
        if (m_isTcpStream)
        {
            if (message.isValid())
            {
                std::string sentinelStr = uxas::common::SentinelSerialBuffer::createSentinelizedString(message.getString());
                LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendMessage BEFORE sending TCP stream single-part message");
                zmq_send(*m_zmqSocket, sentinelStr.c_str(), sentinelStr.size(), ZMQ_SNDMORE);
                LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendMessage AFTER sending TCP stream single-part message");
            }
            else
            {
                LOG_WARN("ZeroMqAddressedAttributedMessageSender::sendMessage failed to create AddressedAttributedMessage object - did not send TCP stream single-part message");
            }
        }
        else
        {
            if (uxas::common::ConfigurationManager::getIsZeroMqMultipartMessage())
            {
                if (message.isValid())
                {
                    LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendMessage BEFORE sending multi-part message");
                    // address
                    n_ZMQ::s_sendmore(*m_zmqSocket, message.getAddress());

                    // contentType
                    n_ZMQ::s_sendmore(*m_zmqSocket, message.getMessageAttributesReference()->getContentType());

                    // descriptor
                    n_ZMQ::s_sendmore(*m_zmqSocket, message.getMessageAttributesReference()->getDescriptor());

                    // source group
                    n_ZMQ::s_sendmore(*m_zmqSocket, message.getMessageAttributesReference()->getSourceGroup());

                    // entity ID
                    n_ZMQ::s_sendmore(*m_zmqSocket, message.getMessageAttributesReference()->getSourceEntityId());

                    // service ID
                    n_ZMQ::s_sendmore(*m_zmqSocket, message.getMessageAttributesReference()->getSourceServiceId());

                    // message payload)
                    n_ZMQ::s_send(*m_zmqSocket, message.getPayload());
                    LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendMessage AFTER sending multi-part message");
                }
                else
                {
                    LOG_WARN("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage ignoring invalid AddressedAttributedMessage object - did not send Zero MQ multi-part message");
                }
            }
            else
            {
                if (message.isValid())
                {
                    LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendMessage BEFORE sending single-part message");
                    n_ZMQ::s_send(*m_zmqSocket, message.getString());
                    LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendMessage AFTER sending single-part message");
                }
                else
                {
                    LOG_WARN("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage failed to create AddressedAttributedMessage object - did not send Zero MQ single-part message");
                }
            }
        }
    } //if(m_zmqSocket)
};

void
ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> message)
{
    if (m_zmqSocket)
    {
        static size_t idSize{0};
        static uint8_t id[256];

        if (m_isTcpStream)
        {
            if (message->isValid())
            {
                if (idSize == 0)
                {
                    memset(id, 0, 256);
                    idSize = 256;
                    m_zmqSocket->getsockopt(ZMQ_IDENTITY, id, &idSize);
                }
                zmq_send(*m_zmqSocket, id, idSize, ZMQ_SNDMORE);

                std::string sentinelStr = uxas::common::SentinelSerialBuffer::createSentinelizedString(message->getString());
                LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage BEFORE sending TCP stream single-part message");
                zmq_send(*m_zmqSocket, sentinelStr.c_str(), sentinelStr.size(), ZMQ_SNDMORE);
                LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage AFTER sending TCP stream single-part message");
            }
            else
            {
                LOG_WARN("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage ignoring invalid AddressedAttributedMessage object - did not send TCP stream single-part message");
            }
        }
        else
        {
            if (uxas::common::ConfigurationManager::getIsZeroMqMultipartMessage())
            {
                if (message->isValid())
                {
                    LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage BEFORE sending multi-part message");
                    // address
                    n_ZMQ::s_sendmore(*m_zmqSocket, message->getAddress());

                    // contentType
                    n_ZMQ::s_sendmore(*m_zmqSocket, message->getMessageAttributesReference()->getContentType());

                    // descriptor
                    n_ZMQ::s_sendmore(*m_zmqSocket, message->getMessageAttributesReference()->getDescriptor());

                    // source group
                    n_ZMQ::s_sendmore(*m_zmqSocket, message->getMessageAttributesReference()->getSourceGroup());

                    // entity ID
                    n_ZMQ::s_sendmore(*m_zmqSocket, message->getMessageAttributesReference()->getSourceEntityId());

                    // service ID
                    n_ZMQ::s_sendmore(*m_zmqSocket, message->getMessageAttributesReference()->getSourceServiceId());

                    // message payload)
                    n_ZMQ::s_send(*m_zmqSocket, message->getPayload());
                    LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage AFTER sending multi-part message");
                }
                else
                {
                    LOG_WARN("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage ignoring invalid AddressedAttributedMessage object - did not send Zero MQ multi-part message");
                }
            }
            else
            {
                if (message->isValid())
                {
                    LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage BEFORE sending single-part message");
                    std::string msg = message->getString();
                    n_ZMQ::s_send(*m_zmqSocket, message->getString());
                    LOG_DEBUG_VERBOSE("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage AFTER sending single-part message");
                }
                else
                {
                    LOG_WARN("ZeroMqAddressedAttributedMessageSender::sendAddressedAttributedMessage ignoring invalid AddressedAttributedMessage object - did not send Zero MQ single-part message");
                }
            }
        }
    } //if(m_zmqSocket)
};

}; //namespace transport
}; //namespace communications
}; //namespace uxas

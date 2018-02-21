// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectNetworkSerialBridge.h"

#include "SerialHelper.h"

#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"

namespace uxas
{
namespace communications
{

LmcpObjectNetworkSerialBridge::LmcpObjectNetworkSerialBridge()
{
};

LmcpObjectNetworkSerialBridge::~LmcpObjectNetworkSerialBridge()
{
    if (m_serialProcessingThread && m_serialProcessingThread->joinable())
    {
        m_serialProcessingThread->detach();
    }
};

bool
LmcpObjectNetworkSerialBridge::configure(const pugi::xml_node& bridgeXmlNode)
{
    bool isSuccess{false};

    if (!bridgeXmlNode.attribute(uxas::common::StringConstant::SerialPortAddress().c_str()).empty())
    {
        m_serialPortAddress = bridgeXmlNode.attribute(uxas::common::StringConstant::SerialPortAddress().c_str()).value();
        isSuccess = true;
        UXAS_LOG_INFORM(s_typeName(), "::configure setting serial port address to ", m_serialPortAddress, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure failed to find serial port address in XML configuration");
    }
    
    if (!bridgeXmlNode.attribute("ConsiderSelfGenerated").empty())
    {
        m_isConsideredSelfGenerated = bridgeXmlNode.attribute("ConsiderSelfGenerated").as_bool();
        UXAS_LOG_INFORM(s_typeName(), "::configure setting 'ConsiderSelfGenerated' boolean to ", m_isConsideredSelfGenerated, " from XML configuration");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::configure did not find 'ConsiderSelfGenerated' boolean in XML configuration; 'ConsiderSelfGenerated' boolean is ", m_isConsideredSelfGenerated);
    }

    if (isSuccess)
    {
        std::string baudRate = bridgeXmlNode.attribute(uxas::common::StringConstant::BaudRate().c_str()).value();
        if (!baudRate.empty())
        {
            m_serialBaudRate = bridgeXmlNode.attribute(uxas::common::StringConstant::BaudRate().c_str()).as_uint();
            UXAS_LOG_INFORM(s_typeName(), "::configure set baud rate to ", baudRate, " from XML configuration ");
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::configure did not find baud rate in XML configuration; retaining default value ", m_serialBaudRate);
        }

        for (pugi::xml_node currentXmlNode = bridgeXmlNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
        {
            if (std::string(uxas::common::StringConstant::SubscribeToMessage().c_str()) == currentXmlNode.name())
            {
                std::string subscriptionAddress = currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).value();
                if (!subscriptionAddress.empty())
                {
                    addSubscriptionAddress(subscriptionAddress);
                }
            }
        }

        //
        // DESIGN 20150911 RJT message addressing - entity ID
        // - received/sent LMCP messages always include entity ID
        // - the entity cast address is derived from entity ID (see getEntityCastAddress function)
        // - bridges never subscribe to the entity cast address on the internal network
        // - bridges usually subscribe (or coordinate subscription) to the entity cast address on external networks
        //   (TCP and serial bridges do not have external subscription)
        //

        // do not forward uni-cast messages addressed to this bridge
        UXAS_LOG_INFORM(s_typeName(), "::configure adding non-forward address [", getNetworkClientUnicastAddress(m_entityId, m_networkId), "]");
        m_nonImportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));
        m_nonExportForwardAddresses.emplace(getNetworkClientUnicastAddress(m_entityId, m_networkId));
    }

    return (isSuccess);
};

bool
LmcpObjectNetworkSerialBridge::initialize()
{
    bool isSuccess{false};

    // initialize the serial connection
    m_serialConnection = uxas::stduxas::make_unique<serial::Serial>(m_serialPortAddress, m_serialBaudRate, serial::Timeout::simpleTimeout(m_serialTimeout_ms));
    if (m_serialConnection->isOpen())
    {
        isSuccess = true;
        UXAS_LOG_INFORM(s_typeName(), "::initialize opened serial connection with serial port address ", m_serialPortAddress, ", baud rate ", m_serialBaudRate, " and timeout ", m_serialTimeout_ms);
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::initialize failed to open serial connection with serial port address ", m_serialPortAddress, ", baud rate ", m_serialBaudRate, " and timeout ", m_serialTimeout_ms);
    }
    
    return (isSuccess);
};

bool
LmcpObjectNetworkSerialBridge::start()
{
    m_serialProcessingThread = uxas::stduxas::make_unique<std::thread>(&LmcpObjectNetworkSerialBridge::executeSerialReceiveProcessing, this);
    UXAS_LOG_INFORM(s_typeName(), "::start serial receive processing thread [", m_serialProcessingThread->get_id(), "]");
    return (true);
};

bool
LmcpObjectNetworkSerialBridge::terminate()
{
    m_isTerminate = true;
    if (m_serialProcessingThread && m_serialProcessingThread->joinable())
    {
        m_serialProcessingThread->join();
        UXAS_LOG_INFORM(s_typeName(), "::terminate calling thread completed m_serialProcessingThread join");
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::terminate unexpectedly could not join m_serialProcessingThread");
    }
    return (true);
};

bool
LmcpObjectNetworkSerialBridge::processReceivedSerializedLmcpMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> 
                                                                   receivedLmcpMessage)
{
    // send message to the external entity
    UXAS_LOG_DEBUGGING(s_typeName(), "::processReceivedSerializedLmcpMessage [", m_entityIdNetworkIdUnicastString, 
            "] before processing serialized message having address ", receivedLmcpMessage->getAddress(),
                  " and size ", receivedLmcpMessage->getPayload().size());

    // process messages from a local service (only)
    if (m_entityIdString == receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId())
    {
        if (m_nonExportForwardAddresses.find(receivedLmcpMessage->getAddress()) == m_nonExportForwardAddresses.end())
        {
            UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage processing message with source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId());
            try
            {
                m_serialConnection->write(uxas::common::SentinelSerialBuffer::createSentinelizedString(receivedLmcpMessage->getString()));
            }
            catch (std::exception& ex)
            {
                std::string errorMessage;
                std::unique_ptr<avtas::lmcp::Object> lmcpServiceStatus = uxas::communications::data::SerialHelper
                        ::createLmcpMessageObjectSerialConnectionFailure(s_typeName(), uxas::communications::data::SerialConnectionAction::WRITE,
                                                                         m_serialPortAddress, m_serialBaudRate, ex, errorMessage);
                sendLmcpObjectBroadcastMessage(std::move(lmcpServiceStatus));
                UXAS_LOG_ERROR(errorMessage, " EXCEPTION: ", ex.what());
            }
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage ignoring non-export message with address ", receivedLmcpMessage->getAddress(), ", source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceServiceId());
        }
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::processReceivedSerializedLmcpMessage ignoring message with source entity ID ", receivedLmcpMessage->getMessageAttributesReference()->getSourceEntityId());
    }

    return (false); // always false implies never terminating bridge from here
};

void
LmcpObjectNetworkSerialBridge::executeSerialReceiveProcessing()
{
    try
    {
        while (!m_isTerminate)
        {
            try
            {
                // check serial connection for inputs
                UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::executeSerialReceiveProcessing [", m_entityIdNetworkIdUnicastString,
                                  "] port [", m_serialConnection->getPort(), "] BEFORE serial connection read");
                std::string serialInput = m_serialConnection->read(static_cast<size_t> (m_serialMaxBytesReadCount));
                UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::executeSerialReceiveProcessing [", m_entityIdNetworkIdUnicastString,
                                  "] port [", m_serialConnection->getPort(), "] AFTER serial connection read value [", serialInput, "]");
                if (!serialInput.empty())
                {
                    UXAS_LOG_DEBUGGING(s_typeName(), "::executeSerialReceiveProcessing [", serialInput, "] before processing received serial string");
                    std::string recvdSerialDataSegment = m_receiveSerialDataBuffer.getNextPayloadString(serialInput);
                    while (!recvdSerialDataSegment.empty())
                    {
                        UXAS_LOG_DEBUGGING(s_typeName(), "::executeSerialReceiveProcessing [", m_entityIdNetworkIdUnicastString, "] processing complete object string segment retrieved from serial buffer");
                        std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> recvdAddAttMsg = uxas::stduxas::make_unique<uxas::communications::data::AddressedAttributedMessage>();
                        if (recvdAddAttMsg->setAddressAttributesAndPayloadFromDelimitedString(std::move(recvdSerialDataSegment)))
                        {
                            if (m_nonImportForwardAddresses.find(recvdAddAttMsg->getAddress()) == m_nonImportForwardAddresses.end())
                            {
                                if(m_isConsideredSelfGenerated)
                                {
                                    recvdAddAttMsg->updateSourceAttributes("SerialBridge", std::to_string(m_entityId), std::to_string(m_networkId));
                                }
                                sendSerializedLmcpObjectMessage(std::move(recvdAddAttMsg));
                            }
                            else
                            {
                                UXAS_LOG_INFORM(s_typeName(), "::executeSerialReceiveProcessing ignoring non-import message with address ", recvdAddAttMsg->getAddress(), ", source entity ID ", recvdAddAttMsg->getMessageAttributesReference()->getSourceEntityId(), " and source service ID ", recvdAddAttMsg->getMessageAttributesReference()->getSourceServiceId());
                            }
                        }
                        else
                        {
                            UXAS_LOG_WARN(s_typeName(), "::executeSerialReceiveProcessing failed to create AddressedAttributedMessage object from serial data buffer string segment");
                        }
                        recvdSerialDataSegment = m_receiveSerialDataBuffer.getNextPayloadString("");
                    }
                }
            }
            catch (std::exception& ex2)
            {
                std::cerr << "Serial exception: " << ex2.what() << std::endl;
                //std::string errorMessage;
                //std::unique_ptr<avtas::lmcp::Object> lmcpServiceStatus = uxas::communications::data::SerialHelper
                //        ::createLmcpMessageObjectSerialConnectionFailure(s_typeName(), uxas::communications::data::SerialConnectionAction::READ, 
                //                                                         m_serialPortAddress, m_serialBaudRate, ex2, errorMessage);
                //sendLmcpObjectBroadcastMessage(std::move(lmcpServiceStatus));
                //UXAS_LOG_ERROR(errorMessage, " EXCEPTION: ", ex2.what());
            }
        }
        std::cerr << "executeSerialReceiveProcessing exiting infinite loop thread" << std::endl;
        UXAS_LOG_INFORM(s_typeName(), "::executeSerialReceiveProcessing exiting infinite loop thread [", std::this_thread::get_id(), "]");
    }
    catch (std::exception& ex)
    {
        std::cerr << "executeSerialReceiveProcessing catching unknown exception: " << ex.what() << std::endl;
        UXAS_LOG_ERROR(s_typeName(), "::executeSerialReceiveProcessing EXCEPTION: ", ex.what());
    }
};

}; //namespace communications
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   TcpBridge.cpp
 * Author: steve
 *
 * Created on March 28, 2014, 3:03 PM
 *
 */

#include "TcpBridge.h"

#include "UxAS_TimerManager.h"
#include "TimeUtilities.h"
#include "UxAS_ZeroMQ.h" // zmq-> s_send, s_sendmore, ...

#include "avtas/lmcp/Factory.h" // getObject (from serial buffer)

#include "zmq.h"
#include "czmq.h"

#include "pugixml.hpp"


#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <iomanip>  //setw, fill, ...


#define STRING_COMPONENT_NAME "TcpBridge"

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_COMPONENT_TYPE "TcpBridge"

#define STRING_XML_SUBSCRIBE_TO_MESSAGE "SubscribeToMessage"
#define STRING_XML_MESSAGE_TYPE "MessageType"
#define STRING_XML_TCP_ADDRESS "TcpAddress"
#define DEFAULT_TCP_ADDRESS "tcp://*:5555"
#define STRING_XML_SERVER "Server"

#define LMCP_MESSAGE_SIZE_MAX (10000)


#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "TCPB-TCPB-TCPB" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "TCPB-TCPB-TCPB" << __FILE__ << ":" << __LINE__ << ":"  << MESSAGE << std::endl;std::cout.flush();

#define RECEIVE_THREAD_CONTROL_ADDRESS "inproc://threadcontrol"

namespace uxas
{
namespace service
{
namespace adapter
{

TcpBridge::ServiceBase::CreationRegistrar<TcpBridge>
TcpBridge::s_registrar(TcpBridge::s_registryServiceTypeNames());

TcpBridge::TcpBridge()
: ServiceBase(TcpBridge::s_typeName(), TcpBridge::s_directoryName()) { };

TcpBridge::~TcpBridge()
{
//    CleanUp();
};

bool
TcpBridge::configure(const pugi::xml_node& ndComponent)
{
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    bool bSucceeded(true);

    if (bSucceeded)
    {
        if (!ndComponent.attribute(STRING_XML_TCP_ADDRESS).empty())
        {
            m_strTcpAddress = ndComponent.attribute(STRING_XML_TCP_ADDRESS).as_string();
        }

        if (!ndComponent.attribute(STRING_XML_SERVER).empty())
        {
            m_bServer = ndComponent.attribute(STRING_XML_SERVER).as_bool();
        }

        for (pugi::xml_node ndCurrent = ndComponent.first_child(); ndCurrent; ndCurrent = ndCurrent.next_sibling())
        {
            if (std::string(STRING_XML_SUBSCRIBE_TO_MESSAGE) == ndCurrent.name())
            {
                std::string strSubscribeToMessage = ndCurrent.attribute(STRING_XML_MESSAGE_TYPE).value();
                if (!strSubscribeToMessage.empty())
                {
                    COUT_FILE_LINE_MSG("Subscribed to [" << strSubscribeToMessage << "]")
                    addSubscriptionAddress(strSubscribeToMessage);
                }
            } //if (std::string(STRING_XML_SUBSCRIBE_TO_MESSAGES) == ndCurrent.name())
        } //for (pugi::xml_node ndCurrent = ndConfigurationEntries.first_child(); ndCurrent; ndCurrent = ndCurrent.next_sibling())
    }

    return (bSucceeded);
}

bool
TcpBridge::initialize()
{
    // open tcp/ip socket for sending/receiving messages
    m_ptr_zmqContextReceive.reset(new zmq::context_t(1));
    m_ptr_ZsckTcpConnection.reset(new zmq::socket_t(*m_ptr_zmqContextReceive, ZMQ_STREAM));
    if (m_bServer)
    {
        m_ptr_ZsckTcpConnection->bind(m_strTcpAddress.c_str());
    }
    else
    {
        m_ptr_ZsckTcpConnection->connect(m_strTcpAddress.c_str());
    }

    return (true);
}

bool
TcpBridge::start()
{
    m_receiveTcpMessagesThread = uxas::stduxas::make_unique<std::thread>(&TcpBridge::ReceiveTcpMessages, this);
    return (true);
};

bool
TcpBridge::terminate()
{
    m_isTerminate = true;
    if (m_receiveTcpMessagesThread && m_receiveTcpMessagesThread->joinable())
    {
        m_receiveTcpMessagesThread->join();
        LOG_INFORM(s_typeName(), "::terminate calling thread completed m_receiveTcpMessagesThread join");
    }
    else
    {
        LOG_WARN(s_typeName(), "::terminate unexpectedly could not join m_receiveTcpMessagesThread");
    }

    if (m_ptr_ZsckTcpConnection)
    {
        uint32_t ui32LingerTime(0);
        m_ptr_ZsckTcpConnection->setsockopt(ZMQ_LINGER, &ui32LingerTime, sizeof (ui32LingerTime));
        m_ptr_ZsckTcpConnection->close();
        // make sure the file is closed
    }
    
    return (true);
}

bool
TcpBridge::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
//    COUT_FILE_LINE_MSG("processReceivedLmcpMessage[" << receivedLmcpMessage->m_object->getFullLmcpTypeName() << "]")
    addMessageToSend(receivedLmcpMessage->m_object);    
    
    return(false);
}

void
TcpBridge::ReceiveTcpMessages()
{
    try
    {
//        while (!m_isTerminate)
        while (true)
        {
            try
            {
                bool bFinished(false);

                //  Process messages from receiver and controller
                zmq::pollitem_t items [] = {
                    { *m_ptr_ZsckTcpConnection, 0, ZMQ_POLLIN, 0}
                };
                size_t szPollTimeOut_ms = 1; //larger numbers limit the speed that messages can be sent

                zmq::poll(&items [0], 1, szPollTimeOut_ms);

                if (items [0].revents & ZMQ_POLLIN) //m_ptr_ZsckTcpConnection
                {
                    // ID first
                    zframe_t* frameid = zframe_recv(*m_ptr_ZsckTcpConnection);
                    memset(m_id, 0, 256);
                    byte* msgid = zframe_data(frameid);
                    size_t msgidsize = zframe_size(frameid);
                    memcpy(m_id, msgid, msgidsize);
                    //std::cerr << "TCPBRIDGE: Received ZMQ ID" << msgid << " of size: " << msgidsize << std::endl;

                    // Data second
                    zframe_t* framedata = zframe_recv(*m_ptr_ZsckTcpConnection);
                    byte* msgdata = zframe_data(framedata);
                    size_t msgsize = zframe_size(framedata);
                    //std::cerr << "TCPBRIDGE: Received ZMQ message of size: " << msgsize << std::endl;

                    std::shared_ptr<avtas::lmcp::Object> ptr_Object;
                    m_ui32MessageCount_Receive_0++;

                    std::string strMessageStream(reinterpret_cast<const char*> (msgdata), msgsize);
                    std::stringstream sstrError;
                    while (bLmcpObjectFromStream(strMessageStream, ptr_Object, sstrError))
                    {
                        std::unique_ptr<avtas::lmcp::Object> ptr_ObjectUnique;
                        ptr_ObjectUnique.reset(ptr_Object->clone());
                        sendLmcpObjectBroadcastMessage(std::move(ptr_ObjectUnique));
//        COUT_FILE_LINE_MSG("Received a Message")
                    }
                    if (!sstrError.str().empty())
                    {
                        CERR_FILE_LINE_MSG(sstrError.str())
                    }
                    zframe_destroy(&frameid);
                    zframe_destroy(&framedata);
                } //if (items [0].revents & ZMQ_POLLIN) //m_ptr_ZsckTcpConnection
                // send messages
                try
                {
                    auto messageToSend = getNextMessageToSend();
                    if(messageToSend)
                    {
                        avtas::lmcp::ByteBuffer* pbbBufferObject = avtas::lmcp::Factory::packMessage(messageToSend.get(), true);
                        std::string message(reinterpret_cast<char*> (pbbBufferObject->array()), pbbBufferObject->capacity());

                        if (m_szSizeID == 0)
                        {
                            m_szSizeID = 256;
                            m_ptr_ZsckTcpConnection->getsockopt(ZMQ_IDENTITY, m_id, &m_szSizeID);
                        }
                        zmq_send(*m_ptr_ZsckTcpConnection, m_id, m_szSizeID, ZMQ_SNDMORE);
                        zmq_send(*m_ptr_ZsckTcpConnection, message.c_str(), message.size(), ZMQ_SNDMORE); // ZMQ_SNDMORE
//                        COUT_FILE_LINE_MSG("Sent a Message[" << messageToSend->getFullLmcpTypeName() << "]")
                    }
                }
                catch (std::exception& e)
                {
                    COUT_FILE_LINE_MSG("processReceivedLmcpMessage exception [ " << e.what() << "]")
                }
                
                
            }
            catch (...)
            {
                CERR_FILE_LINE_MSG("ReceiveTcpMessages::bWorkerFunction exception encountered while receiving HTTP message from tcp/ip[" << m_strTcpAddress << "]")
            }
        }
        CERR_FILE_LINE_MSG(s_typeName() << "::ReceiveTcpMessages exiting infinite loop thread [" << std::this_thread::get_id() << "]");
    }
    catch (std::exception& ex)
    {
        CERR_FILE_LINE_MSG(s_typeName() << "::ReceiveTcpMessages EXCEPTION: " << ex.what());
    }
}

    bool TcpBridge::bLmcpObjectFromStream(std::string& strMessageStream, std::shared_ptr<avtas::lmcp::Object>& ptr_Object, std::stringstream& sstrError)
    {
        bool bCompleteMessage(false);

        //CERR_FILE_LINE_MSG("strMessageStream.size()[" << std::dec  << strMessageStream.size() << "]")
        std::string strNewMessage;
        m_streamBuffer += strMessageStream;
        strMessageStream.clear();
        //CERR_FILE_LINE_MSG("m_streamBuffer.size()[" << std::dec  << m_streamBuffer.size() << "]")
        bool bFinished(false);
        while (!bFinished) //need a while in case there are corrupted strings with LMCP in middle
        {
            std::string strWorking = m_streamBuffer;
            size_t szPositionLMCP = strWorking.find("LMCP");
            if (szPositionLMCP != std::string::npos)
            {
                //CERR_FILE_LINE_MSG("strMessageStream[" << strMessageStream << "]")                    
                // get full string starting at LMCP
                std::string strTempFullString = m_streamBuffer.substr(szPositionLMCP);
                // get length of message, if message is long enough
                if (strTempFullString.size() > (avtas::lmcp::Factory::HEADER_SIZE))
                {
                    size_t szMessageLength = avtas::lmcp::Factory::getObjectSize(reinterpret_cast<const unsigned char*> (strTempFullString.c_str()), avtas::lmcp::Factory::HEADER_SIZE);

                    size_t szMessageLengthTotal = avtas::lmcp::Factory::HEADER_SIZE + szMessageLength + avtas::lmcp::Factory::CHECKSUM_SIZE;
                    //CERR_FILE_LINE_MSG("szMessageLengthTotal[" << std::dec  << szMessageLengthTotal << "]")                    
                    if (szMessageLengthTotal <= LMCP_MESSAGE_SIZE_MAX)
                    {
                        if (strTempFullString.size() >= szMessageLengthTotal)
                        {
                            //CERR_FILE_LINE_MSG("strTempFullString.size()[" << std::dec << strTempFullString.size() << "]")                    
                            strNewMessage = strTempFullString.substr(0, szMessageLengthTotal);
                            if (bLmcpObjectFromString(strNewMessage, ptr_Object, sstrError))
                            {
                                // remove message from buffer
                                m_streamBuffer = strTempFullString.substr(szMessageLengthTotal);
                                bCompleteMessage = true;
                                bFinished = true; // only decode one at a time                       
                            }
                            else
                            {
                                // message was not decoded! Remove LMCP and start again
                                sstrError << "Threw out message bytes! ";
                                m_streamBuffer = m_streamBuffer.substr(szPositionLMCP + 4);
                                bFinished = false;
                                //CERR_FILE_LINE_MSG("Decoded Message: ptr_Object->getLmcpTypeName()[" << ptr_Object->getLmcpTypeName() << "]")
                            }
                        }
                        else //if (strTempFullString.size() >= szMessageLengthTotal)
                        {
                            // string not long enough for message length
                            bFinished = true;
                        } //if (strTempFullString.size() >= szMessageLengthTotal)
                    }
                    else //if(strTempFullString.size() <= LMCP_MESSAGE_SIZE_MAX)
                    {
                        // message length to long! Remove LMCP and start again
                        CERR_FILE_LINE_MSG("message length too long[" << szMessageLengthTotal << "]! Remove LMCP and start again! strMessageStream[" << strMessageStream << "]")
                        m_streamBuffer = m_streamBuffer.substr(szPositionLMCP + 4);
                        bFinished = false;
                    } //if(strTempFullString.size() <= LMCP_MESSAGE_SIZE_MAX)
                }
                else
                {
                    // string not long enough to get size
                    bFinished = true;
                }
            }
            else //if(szPositionLMCP != std:: string::npos)
            {
                // no LMCP in the string
                bFinished = true;
            } //if(szPositionLMCP != std:: string::npos)
        } //while(!bFinished)
        return (bCompleteMessage);
    }

    bool TcpBridge::bLmcpObjectFromString(const std::string& strMessage, std::shared_ptr<avtas::lmcp::Object>& ptr_Object, std::stringstream& sstrError)
    {
        bool bObjectGenerated(false);

        avtas::lmcp::ByteBuffer bbBufferObject;
        bbBufferObject.allocate(strMessage.size());
        bbBufferObject.rewind();

        for (size_t szNumberChars = 0; szNumberChars < strMessage.size(); szNumberChars++)
        {
            bbBufferObject.putByte(strMessage[szNumberChars]);
        }
        bbBufferObject.rewind();

        avtas::lmcp::Object* pObject = avtas::lmcp::Factory::getObject(bbBufferObject);
        if (pObject)
        {
            ptr_Object.reset(pObject);
            pObject = 0;
            bObjectGenerated = true;
        }
        else
        {
            sstrError << "WARNING::bLmcpObjectFromString -  could not convert message string to LMCP object [" << strMessage << "]" << std::endl;
        }
        return (bObjectGenerated);
    };



}; //namespace adapter
}; //namespace service
}; //namespace uxas

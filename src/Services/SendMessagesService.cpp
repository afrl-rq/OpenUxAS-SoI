// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "SendMessagesService.h"

#include "avtas/lmcp/LmcpXMLReader.h"
#include "uxas/messages/uxnative/StartupComplete.h"
#include "uxas/messages/route/GraphRegion.h"
#ifdef AFRL_INTERNAL_ENABLED
#include "uxas/project/isolate/UgsManagementTask.h"
#endif

#include "TimeUtilities.h"
#include "SendMessagesService.h"
#include "Constants/Constant_Strings.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Time.h"

#include <sstream>
#include <iostream>
#include <fstream>
#include <cstdint>

#define STRING_XML_PATH_TO_MESSAGE_FILES "PathToMessageFiles"
#define DEFAULT_PATH_TO_MESSAGE_FILES "SendMessageFiles/"
#define STRING_XML_MESSAGE "Message"
#define STRING_XML_MESSAGE_KEY "MessageKey"
#define STRING_XML_MESSAGE_FILE_NAME "MessageFileName"
#define STRING_XML_MESSAGE_SEND_PERIOD_MS "SendPeriod_ms"
#define STRING_XML_MESSAGE_SEND_NUMBER_TIMES "NumberTimesToSend"
#define STRING_XML_MESSAGE_SEND_TIME_MS "SendTime_ms"

namespace uxas
{
namespace service
{
namespace test
{
SendMessagesService::ServiceBase::CreationRegistrar<SendMessagesService> SendMessagesService::s_registrar(SendMessagesService::s_registryServiceTypeNames());

SendMessagesService::SendMessagesService()
:ServiceBase(SendMessagesService::s_typeName(), ""),
m_messageZeroTime_ms(true)
{
    m_messageZeroTime_ms = uxas::common::utilities::c_TimeUtilities::dGetTimeNow_s(false);
};

SendMessagesService::~SendMessagesService()
{
};

bool
SendMessagesService::configure(const pugi::xml_node& serviceXmlNode)
{
    bool isSuccess{true};

    // get the path to find the message files
    // if relative it will be relative to the start-up directory
    std::string pathToMessages;//(DEFAULT_PATH_TO_MESSAGE_FILES);
    if (!serviceXmlNode.attribute(STRING_XML_PATH_TO_MESSAGE_FILES).empty())
    {
        pathToMessages = serviceXmlNode.attribute(STRING_XML_PATH_TO_MESSAGE_FILES).value();
        pathToMessages = (*(pathToMessages.rbegin()) == '/') ? (pathToMessages) : (pathToMessages + "/"); // make sure it ends with a '/'
    }
    else
    {
        pathToMessages = uxas::common::ConfigurationManager::getInstance()
                .getComponentDataDirectory(s_directoryName());
    }

    bool isFoundMessages(false);
    for (pugi::xml_node currentXmlNode = serviceXmlNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
    {
        if (std::string(STRING_XML_MESSAGE) == currentXmlNode.name())
        {
            bool isGoodMessage(true);

            std::unique_ptr<TestMessage> newMessage(new TestMessage());
            if (!currentXmlNode.attribute(STRING_XML_MESSAGE_FILE_NAME).empty())
            {
                std::string fileName = currentXmlNode.attribute(STRING_XML_MESSAGE_FILE_NAME).value();
                // load the message
//                std::unique_ptr<avtas::lmcp::Object> lmcpObject;
                std::string filePath = pathToMessages + fileName;
                UXAS_LOG_INFORM(s_typeName(), "::configure loading file ", filePath);
                std::ifstream file(filePath.c_str());
                std::string fulltxt;
                if (file.is_open())
                {
                    uint32_t lineCnt{0};
                    while (file.good())
                    {
                        std::string line;
                        lineCnt++;
                        getline(file, line);
                        if (line.c_str()[0] != '#')
                        {
                            fulltxt += line + "\n";
                        }
                    }
                    UXAS_LOG_DEBUGGING(s_typeName(), "::configure loaded XML ", fulltxt);
                    avtas::lmcp::Object* lmcpObj = avtas::lmcp::xml::readXML(fulltxt);
                    isGoodMessage = (lmcpObj != nullptr);
                    if (isGoodMessage)
                    {
                        UXAS_LOG_INFORM(s_typeName(), "::configure created LMCP object from loaded XML");
                        newMessage->m_lmcpObjectPayload.reset(lmcpObj);
                        lmcpObj = nullptr;

                        if (uxas::messages::route::isGraphRegion(newMessage->m_lmcpObjectPayload))
                        {
                            uxas::messages::route::GraphRegion* pGraphRegion = static_cast<uxas::messages::route::GraphRegion*> (newMessage->m_lmcpObjectPayload.get());
                            UXAS_LOG_DEBUGGING(s_typeName(), "::configure loaded ", uxas::messages::route::GraphRegion::TypeName, 
                                          " object with node list size ", pGraphRegion->getNodeList().size(), 
                                          " and edge list size ", pGraphRegion->getEdgeList().size());
                            if (pGraphRegion->getEdgeList().size() > 0)
                            {
                                UXAS_LOG_DEBUGGING(s_typeName(), "::configure loaded ", uxas::messages::route::GraphRegion::TypeName,
                                              " with pGraphRegion->getEdgeList()[0]->getEdgeID() ", pGraphRegion->getEdgeList()[0]->getEdgeID());
                            }
                            pGraphRegion = 0;
                        }
#ifdef AFRL_INTERNAL_ENABLED
                        else if (uxas::project::isolate::isUgsManagementTask(newMessage->m_lmcpObjectPayload))
                        {
                            avtas::lmcp::ByteBuffer* pbbBufferObject = avtas::lmcp::Factory::packMessage(newMessage->m_lmcpObjectPayload.get(), true);
                            std::string strMessageToSave(reinterpret_cast<char*> (pbbBufferObject->array()), pbbBufferObject->capacity());
                            delete pbbBufferObject;
                            std::string fileOutPath = m_workDirectoryPath + "SaveUgsManagementTaskPacked";
                            std::ofstream fileOut(fileOutPath);
                            fileOut << strMessageToSave;
                            fileOut.close();
                            UXAS_LOG_DEBUGGING(s_typeName(), "::configure output ", uxas::project::isolate::UgsManagementTask::TypeName, " to file ", fileOutPath);
                        }
#endif
                    }
                    else
                    {
                        UXAS_LOG_ERROR(s_typeName(), "::configure failed to create LMCP object from loaded XML [",filePath,"]");
                    }
                }
                else
                {
                    UXAS_LOG_ERROR(s_typeName(), "::configure failed to load file ", filePath);
                    isGoodMessage = false;
                }
            }
            else
            {
                isGoodMessage = false;
            }

            if (isGoodMessage)
            {
                if (!currentXmlNode.attribute(STRING_XML_MESSAGE_KEY).empty())
                {
                    newMessage->m_messageAddress = currentXmlNode.attribute(STRING_XML_MESSAGE_KEY).value();
                }
                if (!currentXmlNode.attribute(STRING_XML_MESSAGE_SEND_TIME_MS).empty())
                {
                    newMessage->m_messageSendTime_ms = currentXmlNode.attribute(STRING_XML_MESSAGE_SEND_TIME_MS).as_uint();
                }
                else
                {
                    if (!currentXmlNode.attribute(STRING_XML_MESSAGE_SEND_PERIOD_MS).empty())
                    {
                        newMessage->m_isUseSendTime = false;
                        newMessage->m_messageSendPeriod_ms = currentXmlNode.attribute(STRING_XML_MESSAGE_SEND_PERIOD_MS).as_uint();
                    }
                    if (!currentXmlNode.attribute(STRING_XML_MESSAGE_SEND_NUMBER_TIMES).empty())
                    {
                        newMessage->m_numberTimesToSend = currentXmlNode.attribute(STRING_XML_MESSAGE_SEND_NUMBER_TIMES).as_uint();
                    }
                }

                isFoundMessages = true; // at least found one good message
                m_messagesToSend.push_back(std::move(newMessage));
            }
        }
    }
    if (!isFoundMessages)
    {
        UXAS_LOG_WARN(s_typeName(), "::configure failed to load messages to be sent");
    }
    
    addSubscriptionAddress(uxas::messages::uxnative::StartupComplete::Subscription);

    return (isSuccess);
};

bool
SendMessagesService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    bool isFinished(false);
    
    if (!m_isStartUpComplete 
            && uxas::messages::uxnative::isStartupComplete(receivedLmcpMessage->m_object.get()))
    {
        m_messageZeroTime_ms = uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms();
        m_isStartUpComplete = true;
        isFinished = sendMessages();
    }
    
    return (isFinished);
};

bool
SendMessagesService::sendMessages()
{
    bool isFinished(false);

    int64_t timeFromStart;
    while (!isFinished)
    {
        timeFromStart = uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms() - m_messageZeroTime_ms;
        for (auto itMessage = m_messagesToSend.begin(); itMessage != m_messagesToSend.end();)
        {
            if ((*itMessage)->m_isUseSendTime)
            {
                if (timeFromStart > (*itMessage)->m_messageSendTime_ms)
                {
                    if ((*itMessage)->m_messageAddress.empty())
                    { 
                        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::sendMessages BEFORE sending single-shot broadcast");
                        sendSharedLmcpObjectBroadcastMessage((*itMessage)->m_lmcpObjectPayload);
                        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::sendMessages AFTER sending single-shot broadcast");
                    }
                    else
                    {
                        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::sendMessages BEFORE sending single-shot limited-cast");
                        sendSharedLmcpObjectLimitedCastMessage((*itMessage)->m_messageAddress, (*itMessage)->m_lmcpObjectPayload);
                        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::sendMessages AFTER sending single-shot limited-cast");
                    }
                    itMessage = m_messagesToSend.erase(itMessage); // remove single-shot send message
                }
                else
                {
                    itMessage++;
                }
            }
            else
            {
                if (timeFromStart > (*itMessage)->m_messageSendTime_ms)
                {
                    if ((*itMessage)->m_messageAddress.empty())
                    {
                        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::sendMessages BEFORE sending periodic broadcast");
                        sendSharedLmcpObjectBroadcastMessage((*itMessage)->m_lmcpObjectPayload);
                        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::sendMessages AFTER sending periodic broadcast");
                    }
                    else
                    {
                        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::sendMessages BEFORE sending periodic limited-cast");
                        sendSharedLmcpObjectLimitedCastMessage((*itMessage)->m_messageAddress, (*itMessage)->m_lmcpObjectPayload);
                        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::sendMessages AFTER sending periodic limited-cast");
                    }
                    (*itMessage)->m_messageSendTime_ms += (*itMessage)->m_messageSendPeriod_ms;
                    (*itMessage)->m_numberTimesSent++;
                    if ((*itMessage)->m_numberTimesSent >= (*itMessage)->m_numberTimesToSend)
                    {
                        // this message is all done
                        itMessage = m_messagesToSend.erase(itMessage); // remove periodic send message
                    }
                    else
                    {
                        itMessage++;
                    }
                }
                else
                {
                    itMessage++;
                }
            }
            if (m_messagesToSend.size() < 1)
            {
                isFinished = true;
                break;
            }
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(10));
    }

    return (isFinished);

};

}; //namespace test
}; //namespace service
}; //namespace uxas

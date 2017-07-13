// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "SendTestMessagesService.h"

#include "avtas/lmcp/LmcpXMLReader.h"
#include "uxas/messages/uxnative/StartupComplete.h"
#include "uxas/messages/route/GraphRegion.h"
#ifdef AFRL_INTERNAL_ENABLED
#include "uxas/project/isolate/UgsManagementTask.h"
#endif

#include "TimeUtilities.h"
//#include "SendMessagesService.h"
#include "Constants/Constant_Strings.h"
#include "STaliroCommInterface.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Time.h"

#include <sstream>
#include <iostream>
#include <fstream>
#include <cstdint>

#include <vector>
#include <string>
#include "avtas/lmcp/Object.h"
#include "avtas/lmcp/Node.h"
#include "avtas/lmcp/NodeUtil.h"
#include "avtas/lmcp/XMLParser.h"
#include "afrl/cmasi/AirVehicleState.h"

#define STRING_XML_TEST_GENERATOR_PORT "TestGeneratorPort"

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
SendTestMessagesService::ServiceBase::CreationRegistrar<SendTestMessagesService> 
SendTestMessagesService::s_registrar(SendTestMessagesService::s_registryServiceTypeNames());
    
SendTestMessagesService::SendTestMessagesService()
{
    m_messageZeroTime_ms = uxas::common::utilities::c_TimeUtilities::dGetTimeNow_s(false);
};

SendTestMessagesService::~SendTestMessagesService()
{
};

bool
SendTestMessagesService::configure(const pugi::xml_node& serviceXmlNode)
{
    bool isSuccess{true};
    std::map<std::string, std::map<std::string, std::string> > fileFieldMap;
    std::map<std::string, std::map<std::string, std::string> >::iterator fileFieldMapIter;
    std::map<std::string, std::map<std::string, std::vector<double> > taskFileFieldMap;
    std::map<std::string, std::map<std::string, std::vector<double> >::iterator taskFileFieldMapIter;
    
    //bool doesTestGeneratorExist{false};
    int testGeneratorInterfacePort;

    if (!serviceXmlNode.attribute(STRING_XML_TEST_GENERATOR_PORT).empty())
    {
        testGeneratorInterfacePort = serviceXmlNode.attribute(STRING_XML_TEST_GENERATOR_PORT).as_uint();
        UXAS_LOG_DEBUGGING(s_typeName(), "::configure Accepting connection from the test generator at port: ", testGeneratorInterfacePort);

        // Get connection from the test generator (S-TaLiRo) and get field name and value pairs.
        staliroInterface = testgeneration::staliro::c_CommunicationInterface::getInstance();
        staliroInterface->createServer(testGeneratorInterfacePort);
        staliroInterface->acceptConnection();
        staliroInterface->setFileFieldMapPtr(&fileFieldMap);
        staliroInterface->setTaskFileFieldMapPtr(&taskFileFieldMap);
        staliroInterface->receiveCommands();
    }
    else
    {
        UXAS_LOG_DEBUGGING(s_typeName(), "::configure No test generator exists.");
    }
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


                    Node* el = avtas::lmcp::XMLParser::parseString(fulltxt, false);
                    std::vector <Node*> childList;
                    if (el != nullptr)
                    {
                        fileFieldMapIter = fileFieldMap.find(fileName);
                        if (fileFieldMapIter != fileFieldMap.end())
                        {
                            for (std::map<std::string, std::string>::iterator fieldMapIter = fileFieldMapIter->second.begin(); 
                                    fieldMapIter != fileFieldMapIter->second.end(); 
                                    fieldMapIter++)
                            {
                                std::vector<std::string> fieldNameVector = avtas::lmcp::NodeUtil::splitString(fieldMapIter->first, '.');
                                std::vector<std::string>::iterator fieldNameVectorIter = fieldNameVector.begin();
                                if (el->getTagName() == *fieldNameVectorIter)
                                {
                                    bool isFieldFound{true};
                                    fieldNameVectorIter++;
                                    Node* curNode = el;
                                    
                                    for (; fieldNameVectorIter != fieldNameVector.end(); fieldNameVectorIter++)
                                    {
                                        childList = avtas::lmcp::NodeUtil::getList(curNode, *fieldNameVectorIter);
                                        if (childList.empty())
                                        {
                                            isFieldFound = false;
                                            break;
                                        }
                                        int childInd = 0;
                                        if (childList.size() > 1)
                                        {
                                            // In this case, the next field name must be the index
                                            fieldNameVectorIter++;
                                            if (fieldNameVectorIter != fieldNameVector.end() && (*fieldNameVectorIter)[0] >= '0' && (*fieldNameVectorIter)[0] <= '9')
                                            {
                                                childInd = std::stoi(*fieldNameVectorIter, nullptr, 10)-1; // -1 to convert from MATLAB indexing to C++
                                                curNode = childList[childInd];
                                            }
                                            else
                                            {
                                                // Next field name was not a number. So, roll back the increment and use 0 as child index.
                                                fieldNameVectorIter--;
                                                curNode = childList[0];
                                            }
                                        }
                                        else
                                        {
                                            curNode = childList[0];
                                        }
                                    }
                                    if (fieldNameVectorIter != fieldNameVector.end() || curNode->getChildCount() != 0)
                                    {
                                        // Either the given fieldname of the Node has one more child
                                        isFieldFound = false;
                                    }
                                    if (isFieldFound)
                                    {
                                        curNode->setText(fieldMapIter->second);
                                    }
                                }
                            }
                        }
                        
                        taskFileFieldMapIter = taskFileFieldMap.find(fileName);
                        if (taskFileFieldMapIter != taskFileFieldMap.end())
                        {
                            
                        }
                    }

                    
                    avtas::lmcp::Object* lmcpObj = avtas::lmcp::xml::readXML(el);
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
                        UXAS_LOG_ERROR(s_typeName(), "::configure failed to create LMCP object from loaded XML");
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
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    //staliroInterface->closeConnection();

    return (isSuccess);
};

bool
SendTestMessagesService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
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

}; //namespace test
}; //namespace service
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_SERVICE_TEST_SEND_MESSAGES_TEST_SERVICE_H
#define UXAS_SERVICE_TEST_SEND_MESSAGES_TEST_SERVICE_H



#include "ServiceBase.h"

namespace uxas
{
namespace service
{
namespace test
{

/*! \class SendMessagesService
 *\brief . 
 * @par Description:     
 * The <B><i>SendMessagesService</i></B> sends out messages, loaded from files, 
 * at a given time or periodically
 * 
 * Configuration String: 
  *  <Service Type="SendMessagesService" PathToMessageFiles="SendMessageFiles/">
 *      <Message MessageFileName="AirVehicleConfiguration_V1000.xml" SendTime_ms="50"/>
 *  </Service>
 * 
 * Options:
 *  - PathToMessageFiles
 *  - - Message
 *  - - MessageFileName
 *  - - SendPeriod_ms
 *  - - NumberTimesToSend
 *  - - SendTime_ms
 * 
 * Subscribed Messages:
 *  - uxas::messages::uxnative::StartupComplete
 * 
 * Sent Messages:
 *  - messages found in Message entries
 * 
 */

class SendMessagesService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("SendMessagesService"); return (s_string); };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() { static std::string s_string("SendMessagesService"); return (s_string); };

    static ServiceBase*
    create()
    {
        return new SendMessagesService;
    };

    SendMessagesService();

    virtual
    ~SendMessagesService();

protected:

    static
    ServiceBase::CreationRegistrar<SendMessagesService> s_registrar;

    /** \brief Copy construction not permitted */
    SendMessagesService(SendMessagesService const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(SendMessagesService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

    bool
    sendMessages();
    
    /** \class TestMessage
        \brief Data object containing LMCP object and test-related attributes.
     */
    struct TestMessage
    {

        TestMessage() :
        m_isUseSendTime(true), m_messageSendTime_ms(0),
        m_messageSendPeriod_ms(0), m_messageNextSendTime_ms(0),
        m_numberTimesToSend(UINT32_MAX), m_numberTimesSent(0) { };

        std::shared_ptr<avtas::lmcp::Object> m_lmcpObjectPayload;
        std::string m_messageAddress;
        bool m_isUseSendTime;
        uint32_t m_messageSendTime_ms;
        uint32_t m_messageSendPeriod_ms;
        uint32_t m_messageNextSendTime_ms;
        uint32_t m_numberTimesToSend;
        uint32_t m_numberTimesSent;
    };

    /** \brief  container of @ref TestMessage used to send messages at correct times.*/
    std::vector<std::shared_ptr<TestMessage>> m_messagesToSend;
    /** \brief  time that the "StartupComplete" message was received. Initialized
     * to construction time.*/
    int64_t m_messageZeroTime_ms;
    /** \brief keeps track of start up status, in case extra startupcomplete
     * messages are received */
    bool m_isStartUpComplete = {false};

};

}; //namespace test
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TEST_SEND_MESSAGES_TEST_SERVICE_H */

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_SERVICE_SEND_TEST_MESSAGES_SERVICE_H
#define UXAS_SERVICE_SEND_TEST_MESSAGES_SERVICE_H

#include "SendMessagesService.h"
#include "STaliroCommInterface.h"

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
  *  <Service Type="SendTestMessagesService" PathToMessageFiles="SendMessageFiles/">
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

class SendTestMessagesService : public SendMessagesService
{
public:
    using ServiceBase::ServiceBase;
    static const std::string&
    s_typeName() { static std::string s_string("SendTestMessagesService"); return (s_string); };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() { static std::string s_string("SendTestMessagesService"); return (s_string); };

    static ServiceBase*
    create()
    {
        return new SendTestMessagesService;
    };

    SendTestMessagesService();

    virtual
    ~SendTestMessagesService();
    
    testgeneration::staliro::c_CommunicationInterface* staliroInterface;

private:

    static
    ServiceBase::CreationRegistrar<SendTestMessagesService> s_registrar;

    /** \brief Copy construction not permitted */
    SendTestMessagesService(SendTestMessagesService const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(SendTestMessagesService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;
    
    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;
};

}; //namespace test
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_SEND_TEST_MESSAGES_SERVICE_H */

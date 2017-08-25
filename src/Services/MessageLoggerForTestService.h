// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_SERVICE_MESSAGE_LOGGER_FOR_TEST_SERVICE_H
#define UXAS_SERVICE_MESSAGE_LOGGER_FOR_TEST_SERVICE_H

#include "ServiceBase.h"
#include <map>
#include "STaliroTrajectoryPopulator.h"
#include "STaliroCommInterface.h"

namespace uxas
{
namespace service
{
namespace test
{


/*! \class MessageLoggerForTestService
 *\brief Description:     
 * The <B><i>MessageLoggerForTestService</i></B> logs messages received from other 
 * UxAS services and send to test generator. Messages to send should be configured.
 * 
 * 
 * Configuration String: 
 *  <Service Type="MessageLoggerForTestService">
 *      <LogMessage MessageType="uxas.messages.task.AssignmentCostMatrix"/>
 *  </Service>
 *
 * 
 * Subscribed Messages:
 *  - all those in "LogMessage" entries
 * 
 * Sent Messages:
 *  none 
 * 
 */

class MessageLoggerForTestService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("MessageLoggerForTestService"); return (s_string); };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() { static std::string s_string(""); return (s_string); };

    static ServiceBase*
    create() { return new MessageLoggerForTestService; };

    MessageLoggerForTestService();

    virtual
    ~MessageLoggerForTestService();

    testgeneration::staliro::c_CommunicationInterface* staliroInterface;
    
private:

    static
    ServiceBase::CreationRegistrar<MessageLoggerForTestService> s_registrar;

    /** \brief Copy construction not permitted */
    MessageLoggerForTestService(MessageLoggerForTestService const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(MessageLoggerForTestService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;
    
    void sendOutTrajectory();
    void sendMonitorResults();
    
    std::map<int64_t, std::vector<double_t>> trajectory;
    std::map<int64_t, int32_t> taskStatusResults;
    std::map<int64_t, double_t> taskRobustnessResults;
    std::map<int32_t, std::vector<std::string>> trajectoryMapping;
    testgeneration::staliro::c_TrajectoryPopulator *staliroTrajectoryPopulator;
};

}; //namespace test
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_MESSAGE_LOGGER_FOR_TEST_SERVICE_H */

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_SERVICE_DATA_MESSAGE_LOGGER_DATA_SERVICE_H
#define UXAS_SERVICE_DATA_MESSAGE_LOGGER_DATA_SERVICE_H



#include "ServiceBase.h"

#include "UxAS_DatabaseLogger.h"
#include "UxAS_FileLogger.h"

//#include "UxAS_TypeDefs_String.h"

namespace uxas
{
namespace service
{
namespace data
{


/*! \class MessageLoggerDataService
 *\brief Description:     
 * The <B><i>MessageLoggerDataService</i></B> logs messages received from other 
 * UxAS services to a files in a directory.  Logging can be configured to log 
 * either all or a subset of service messages.
 * 
 * 
 * Configuration String: 
 *  <Service Type="MessageLoggerDataService" LogFileMessageCountLimit="10000">
 *      <LogMessage MessageType="uxas.messages.task.AssignmentCostMatrix" />
 *  </Service>
 *
 * Options:
 *  - LogFileMessageCountLimit
 *     (if provided, turns on additional plain text file logging with each
 *      file containing 'LogFileMessageCountLimit' number of messages)
 * 
 * Subscribed Messages:
 *  - all those in "LogMessage" entries
 * 
 * Sent Messages:
 *  none 
 * 
 */

class MessageLoggerDataService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("MessageLoggerDataService"); return (s_string); };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() { static std::string s_string("SavedMessages"); return (s_string); };

    static ServiceBase*
    create() { return new MessageLoggerDataService; };

    MessageLoggerDataService();

    virtual
    ~MessageLoggerDataService();

public:
    /** \brief This is the full path to the (initial?) log file */
    std::string m_logFilePath;
    
private:

    static
    ServiceBase::CreationRegistrar<MessageLoggerDataService> s_registrar;

    /** \brief Copy construction not permitted */
    MessageLoggerDataService(MessageLoggerDataService const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(MessageLoggerDataService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

    bool isDatabaseLogger{true};  // always save to database log
    bool isFileLogger{false};     // only save to file if message count limit provided
    uint32_t m_logDatabaseMessageCountLimit{UINT32_MAX};
    uint32_t m_logFileMessageCountLimit{0};
    std::unique_ptr<uxas::common::log::LoggerBase> m_databaseLogger;
    std::unique_ptr<uxas::common::log::LoggerBase> m_fileLogger;

};

}; //namespace data
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_DATA_MESSAGE_LOGGER_DATA_SERVICE_H */

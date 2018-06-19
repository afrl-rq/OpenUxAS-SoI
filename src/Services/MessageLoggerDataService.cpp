// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "MessageLoggerDataService.h"

#include "UxAS_DatabaseLogger.h"
#include "UxAS_FileLogger.h"
#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"
#include "UxAS_XmlUtil.h"

#include "FileSystemUtilities.h"

#include <chrono>
#include <thread>
#include <cstdint>

namespace uxas
{
namespace service
{
namespace data
{

MessageLoggerDataService::ServiceBase::CreationRegistrar<MessageLoggerDataService> 
        MessageLoggerDataService::s_registrar(MessageLoggerDataService::s_registryServiceTypeNames());

MessageLoggerDataService::MessageLoggerDataService()
: ServiceBase(MessageLoggerDataService::s_typeName(), MessageLoggerDataService::s_directoryName())
{
};

MessageLoggerDataService::~MessageLoggerDataService()
{
    if (m_databaseLogger)
    {
        m_databaseLogger->closeStream();
    }
    
    if (m_fileLogger)
    {
        m_fileLogger->closeStream();
    }
};

bool
MessageLoggerDataService::configure(const pugi::xml_node& serviceXmlNode)
{
    if (!serviceXmlNode.attribute(uxas::common::StringConstant::LogFileMessageCountLimit().c_str()).empty())
    {
        uint32_t logFileMsgCntLimFromXml = serviceXmlNode.attribute(uxas::common::StringConstant::LogFileMessageCountLimit().c_str()).as_uint();
        if (logFileMsgCntLimFromXml > 0 && logFileMsgCntLimFromXml <= UINT32_MAX)
        {
            m_logFileMessageCountLimit = logFileMsgCntLimFromXml;
            UXAS_LOG_INFORM(s_typeName(), "::configure set m_logFileMessageCountLimit value to ", m_logFileMessageCountLimit, " from XML");
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::configure retaining m_logFileMessageCountLimit value ", m_logFileMessageCountLimit, "; ignoring invalid value from XML");
        }
    }
    
    for (pugi::xml_node currentXmlNode = serviceXmlNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
    {
        if (std::string("LogMessage") == currentXmlNode.name())
        {
            std::string messageType = currentXmlNode.attribute(uxas::common::StringConstant::MessageType().c_str()).value();
            if (!messageType.empty())
            {
                addSubscriptionAddress(messageType);
            }
        }
    }

    return (true);
};

bool
MessageLoggerDataService::initialize()
{
    bool isDatabaseLoggerSuccess{true};
    auto isTimeStamp = uxas::common::ConfigurationManager::getIsDataTimeStamp();

    if (isDatabaseLogger)
    {
        m_databaseLogger = uxas::common::log::LoggerBase::instantiateLogger(uxas::common::log::DatabaseLogger::s_typeName());
        isDatabaseLoggerSuccess = m_databaseLogger->configure(m_workDirectoryPath + "messageLog", isTimeStamp, false, m_logDatabaseMessageCountLimit);

        if (isDatabaseLoggerSuccess)
        {
            std::string dbTableColumnNames{"id,time_ms,descriptor,groupID,entityID,serviceID,xml"};

            std::string dbTableName{"msg"};

            std::string dbTableCreate{"CREATE TABLE msg ("};
            dbTableCreate.append("id INTEGER PRIMARY KEY");
            dbTableCreate.append(", time_ms INTEGER NOT NULL");
            dbTableCreate.append(", descriptor TEXT NOT NULL");
            dbTableCreate.append(", groupID TEXT NOT NULL");
            dbTableCreate.append(", entityID INTEGER NOT NULL");
            dbTableCreate.append(", serviceID INTEGER NOT NULL");
            dbTableCreate.append(", xml BLOB NOT NULL)");

            isDatabaseLoggerSuccess = static_cast<uxas::common::log::DatabaseLogger*>(m_databaseLogger.get())->configureDatabase(dbTableCreate, dbTableName, dbTableColumnNames);
        }

        if (isDatabaseLoggerSuccess)
        {
            isDatabaseLoggerSuccess = m_databaseLogger->openStream(m_logFilePath);
        }

        if (isDatabaseLoggerSuccess)
        {
            UXAS_LOG_INFORM(s_typeName(), "::initialize instantiated DatabaseLogger");
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::initialize failed to instantiate DatabaseLogger");
        }
    }
    
    bool isFileLoggerSuccess{true};
    if (isFileLogger)
    {
        m_fileLogger = uxas::common::log::LoggerBase::instantiateLogger(uxas::common::log::FileLogger::s_typeName());
        isFileLoggerSuccess = m_fileLogger->configure(m_workDirectoryPath + "messageLog", isTimeStamp, m_logFileMessageCountLimit);

        if (isFileLoggerSuccess)
        {
            isFileLoggerSuccess = m_fileLogger->openStream(m_logFilePath);
        }

        if (isFileLoggerSuccess)
        {
            UXAS_LOG_INFORM(s_typeName(), "::initialize instantiated FileLogger");
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::initialize failed to instantiate FileLogger");
        }
    }
    
    return (isDatabaseLoggerSuccess && isFileLoggerSuccess);
};

bool
MessageLoggerDataService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::processReceivedLmcpMessage BEFORE logging received message");
    
    if (m_databaseLogger)
    {
        std::string XML = receivedLmcpMessage->m_object->toXML();
        //uxas::common::XmlUtil::escapeXmlQuoteApostropheChars(XML);
        m_databaseLogger->outputTextToStream("NULL,'" +
                std::to_string(uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms()) + "','" +
                receivedLmcpMessage->m_attributes->getDescriptor() + "','" +
                receivedLmcpMessage->m_attributes->getSourceGroup() + "','" +
                receivedLmcpMessage->m_attributes->getSourceEntityId() + "','" +
                receivedLmcpMessage->m_attributes->getSourceServiceId() + "','" +
                XML + "'");
    }
    
    if (m_fileLogger)
    {
        m_fileLogger->outputTimeTextToStream(receivedLmcpMessage->m_attributes->getString());
        m_fileLogger->outputTextToStream(receivedLmcpMessage->m_object->toXML());
    }
    
    UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::processReceivedLmcpMessage AFTER logging received message");

    return (false); // always false implies never terminating service from here
};

}; //namespace data
}; //namespace service
}; //namespace uxas

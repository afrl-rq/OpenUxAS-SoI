// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_HeadLogDataDatabaseLogger.h"

#include "UxAS_Time.h"

#include "stdUniquePtr.h"
#include "UxAS_XmlUtil.h"

namespace uxas
{
namespace common
{
namespace log
{

HeadLogDataDatabaseLogger::LoggerBase::CreationRegistrar<HeadLogDataDatabaseLogger> HeadLogDataDatabaseLogger::s_registrar(s_typeName());

HeadLogDataDatabaseLogger::HeadLogDataDatabaseLogger()
: LoggerBase(s_typeName())
{
};

HeadLogDataDatabaseLogger::~HeadLogDataDatabaseLogger()
{
    if (m_HeadLogDataDatabaseLoggerHelper)
    {
        m_HeadLogDataDatabaseLoggerHelper->closeStream();
    }
};

bool
HeadLogDataDatabaseLogger::configure(const std::string& location, const bool isTimestamp, const bool isLogThreadId, const uint32_t loggerStatementCountLimit)
{
    m_location = location;
    m_isTimestamp = isTimestamp;
    m_isLogThreadId = isLogThreadId;
    m_loggerStatementCountLimit = loggerStatementCountLimit;
    m_HeadLogDataDatabaseLoggerHelper = uxas::stduxas::make_unique<DatabaseLoggerHelper>();
    
    std::string dbTableColumnNames{"time_ms"};
    if (m_isLogThreadId)
    {
        dbTableColumnNames.append(",threadId");
    }
    dbTableColumnNames.append(",severityLevel");
    dbTableColumnNames.append(",text");

    std::string dbTableName{"log"};

    std::string dbTableCreate{"CREATE TABLE log ("};
    dbTableCreate.append("id INTEGER PRIMARY KEY");
    dbTableCreate.append(", time_ms INTEGER NOT NULL");
    if (m_isLogThreadId)
    {
        dbTableCreate.append(", threadId TEXT NOT NULL");
    }
    dbTableCreate.append(", severityLevel TEXT NOT NULL");
    dbTableCreate.append(", text BLOB NOT NULL)");

    return(m_HeadLogDataDatabaseLoggerHelper->configureDatabaseHelper(m_location, m_isTimestamp, m_loggerStatementCountLimit, 
                                                               dbTableCreate, dbTableName, dbTableColumnNames));
};

bool
HeadLogDataDatabaseLogger::openStream(std::string& logFilePath)
{
    return (m_HeadLogDataDatabaseLoggerHelper->openStream(logFilePath));
};

bool
HeadLogDataDatabaseLogger::closeStream()
{
    return (m_HeadLogDataDatabaseLoggerHelper->closeStream());
};

bool
HeadLogDataDatabaseLogger::outputToStream(HeadLogData& headerAndData)
{
    std::string msg = headerAndData.m_message.str().substr();
    uxas::common::XmlUtil::escapeXmlQuoteApostropheChars(msg);
    m_HeadLogDataDatabaseLoggerHelper->insertValuesIntoTable("'" + std::to_string(headerAndData.m_time_ms) + "','" +
                                                             (m_isLogThreadId ? (headerAndData.m_threadID.str() + "','") : "") +
                                                             headerAndData.m_severityLevelString + "','" +
                                                             msg + "'");
    return true;
};

}; //namespace log
}; //namespace common
}; //namespace uxas

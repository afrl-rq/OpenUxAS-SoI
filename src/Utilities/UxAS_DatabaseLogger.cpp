// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_DatabaseLogger.h"

#include "stdUniquePtr.h"

namespace uxas
{
namespace common
{
namespace log
{

DatabaseLogger::LoggerBase::CreationRegistrar<DatabaseLogger> DatabaseLogger::s_registrar(s_typeName());

DatabaseLogger::DatabaseLogger()
: LoggerBase(s_typeName())
{
    m_databaseLoggerHelper = uxas::stduxas::make_unique<DatabaseLoggerHelper>();
};

DatabaseLogger::~DatabaseLogger()
{
    if (m_databaseLoggerHelper)
    {
        m_databaseLoggerHelper->closeStream();
    }
};

bool
DatabaseLogger::configureDatabase(const std::string& createDatabase, const std::string& databaseTableName, const std::string& databaseTableColumnNames)
{
    return (m_databaseLoggerHelper->configureDatabaseHelper(m_location, m_isTimestamp, m_loggerStatementCountLimit, createDatabase, databaseTableName, databaseTableColumnNames));
};
    
bool
DatabaseLogger::openStream(std::string& logFilePath)
{
    return (m_databaseLoggerHelper->openStream(logFilePath));
};

bool
DatabaseLogger::closeStream()
{
    return (m_databaseLoggerHelper->closeStream());
};

bool
DatabaseLogger::outputTextToStream(const std::string& text)
{
    return (m_databaseLoggerHelper->insertValuesIntoTable(text));
};

}; //namespace log
}; //namespace common
}; //namespace uxas

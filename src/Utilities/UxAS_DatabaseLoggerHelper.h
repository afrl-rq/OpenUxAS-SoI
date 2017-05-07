// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_DATABASE_LOGGER_HELPER_H
#define UXAS_COMMON_LOG_DATABASE_LOGGER_HELPER_H

#include <SQLiteCpp/Database.h>
#include <SQLiteCpp/SQLiteCpp.h>

#include <fstream>
#include <memory>
#include <string>

namespace uxas
{
namespace common
{
namespace log
{

class DatabaseLoggerHelper
{
public:

    DatabaseLoggerHelper();

    ~DatabaseLoggerHelper();

private:

    // \brief Prevent copy construction
    DatabaseLoggerHelper(const DatabaseLoggerHelper&) = delete;

    // \brief Prevent copy assignment operation
    DatabaseLoggerHelper& operator=(const DatabaseLoggerHelper&) = delete;

public:

    bool
    configureDatabaseHelper(const std::string& location, bool isTimestamp, const uint32_t statementCountLimit, const std::string& createDatabase, const std::string& databaseTableName, const std::string& databaseTableColumnNames);
    
    bool
    openStream(std::string& logFilePath);

    bool
    closeStream();

    bool
    insertValuesIntoTable(const std::string& commaDelimitedValues);

private:

    bool
    closeAndOpenStream();
    
    std::string m_location;
    bool m_isTimestamp{true};
    
    std::string m_dbFilePath;
    std::string m_dbFilePathOld;
    std::string m_dbFilePathCloseFailed;
    uint32_t m_dbFileCount{0};
    uint32_t m_dbStatementCount{1};
    uint32_t m_dbStatementCountLimit{2000};
    uint32_t m_dbFileCloseFailureCount{0};
    
    std::unique_ptr<SQLite::Database> m_db;
    bool m_isTableConfigurationDefined{false};
    bool m_isDbOpened{false};
    std::string m_dbTableCreate;
    std::string m_dbTableName;
    std::string m_dbTableColumnNames;
    
};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_LOG_DATABASE_LOGGER_HELPER_H */

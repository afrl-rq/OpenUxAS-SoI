// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_DatabaseLoggerHelper.h"

#include "UxAS_Time.h"
#include "UxAS_XmlUtil.h"

#include "stdUniquePtr.h"

#include <iostream>

namespace uxas
{
namespace common
{
namespace log
{

DatabaseLoggerHelper::DatabaseLoggerHelper()
{
};

DatabaseLoggerHelper::~DatabaseLoggerHelper()
{
    closeStream();
};

bool
DatabaseLoggerHelper::configureDatabaseHelper(const std::string& location, bool isTimestamp, const uint32_t statementCountLimit, const std::string& createDatabase, const std::string& databaseTableName, const std::string& databaseTableColumnNames)
{
    if (createDatabase.size() < 20 || databaseTableName.size() < 1 || databaseTableColumnNames.size() < 1
            || (createDatabase.find("CREATE") == std::string::npos && createDatabase.find("create") == std::string::npos))
    {
        std::cout << "ERROR: DatabaseLoggerHelper::configureDatabaseHelper failed due to invalid database definition" << std::endl;
        return (false);
    }
    m_location = location;
    m_isTimestamp = isTimestamp;
    m_dbStatementCountLimit = statementCountLimit;
    m_dbTableCreate = createDatabase;
    m_dbTableName = databaseTableName;
    m_dbTableColumnNames = databaseTableColumnNames;
    m_isTableConfigurationDefined = true;
    return (true);
};

bool
DatabaseLoggerHelper::openStream(std::string& logFilePath)
{
    if (!m_isTableConfigurationDefined)
    {
        return (false);
    }
    
    bool isSuccess{false};
    m_dbFilePathOld = m_dbFilePath;
    m_dbFilePath = m_location + '_' + std::to_string(++m_dbFileCount) 
            + (m_isTimestamp ? ('_' + std::to_string(uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms())) : "") + ".db3";
    logFilePath = m_dbFilePath;
    // initialize SQLite database
    try
    {
        std::ifstream dbFile(m_dbFilePath);
        if (dbFile.is_open())
        {
            dbFile.close();
            remove(m_dbFilePath.c_str());
        }
            m_db = uxas::stduxas::make_unique<SQLite::Database>(m_dbFilePath, SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE);

            // begin transaction
            SQLite::Transaction createTableTrans(*(m_db.get()));
            m_db->exec(m_dbTableCreate);

            // commit transaction
            createTableTrans.commit();
        
        m_isDbOpened = true;
        isSuccess = true;
    }
    catch (std::exception& ex)
    {
        std::cout << "ERROR: DatabaseLoggerHelper::openStream failed to open database file and create SQLite tables [" << m_dbFilePath << "] - ERROR: [" << ex.what() << "]" << std::endl;
    }

    return (isSuccess);
};

bool
DatabaseLoggerHelper::closeStream()
{
    bool isSuccess{false};
    if (m_db)
    {
        std::string dbFilePath = m_db->getFilename();
        try
        {
            m_db.reset();
            isSuccess = true;
        }
        catch (std::exception& ex)
        {
            std::cout << "ERROR: DatabaseLoggerHelper::closeStream failed to close database file [" << dbFilePath << "] - ERROR: [" << ex.what() << "]" << std::endl;
            if (!m_dbFilePathOld.empty())
            {
                m_dbFilePathCloseFailed = m_dbFilePathOld;
                m_dbFileCloseFailureCount++;
                std::cout << "ERROR: DatabaseLoggerHelper::closeStream close database file failure count [" << dbFilePath << std::endl;
            }
        }
    }

    return (isSuccess);
};

bool
DatabaseLoggerHelper::insertValuesIntoTable(const std::string& commaDelimitedValues)
{
    bool isSuccess{true};
    if (!m_isDbOpened)
    {
        std::string logFilePath;
        isSuccess = openStream(logFilePath);
    }
    if (isSuccess)
    {
        std::string insertSqlStmt = "INSERT INTO " + m_dbTableName + " (" + m_dbTableColumnNames + ") VALUES (" + commaDelimitedValues + ")";
        try
        {
            // begin transaction
            SQLite::Transaction transaction(*(m_db.get()));
            m_db->exec(insertSqlStmt);
            // commit transaction
            transaction.commit();
            m_dbStatementCount++;
            isSuccess = closeAndOpenStream();
        }
        catch (std::exception& ex)
        {
            std::cout << "ERROR: DatabaseLoggerHelper::insertMessageIntoTable insert failed while executing SQL statement [" << insertSqlStmt << "] - ERROR: [" << ex.what() << "]" << std::endl;
        }
    }
    return (isSuccess);
};

bool
DatabaseLoggerHelper::closeAndOpenStream()
{
    bool isSuccess{true};
    if (m_dbStatementCount > m_dbStatementCountLimit)
    {
        if (!closeStream())
        {
            isSuccess = false;
            std::cout << "WARN: DatabaseLoggerHelper::closeAndOpenStream failed to close database file [" << m_dbFilePathOld << "]" << std::endl;
        }
        std::string logFilePath;        //not used ??
        if (!openStream(logFilePath))
        {
            isSuccess = false;
            std::cout << "WARN: DatabaseLoggerHelper::closeAndOpenStream failed to open database file" << std::endl;
        }
        m_dbStatementCount = 1;
        if (!m_dbFilePathOld.empty() && m_dbFileCloseFailureCount > 0)
        {
            if (m_dbFilePathCloseFailed.size() > 0)
            {
                std::cout << "WARN: DatabaseLoggerHelper::closeAndOpenStream failed to close database file [" << m_dbFilePathCloseFailed << "]" << std::endl;
                m_dbFilePathCloseFailed = "";
            }
            std::cout << "WARN: DatabaseLoggerHelper::closeAndOpenStream close database file failure count [" << m_dbFileCloseFailureCount << "]" << std::endl;
        }
    }
    return (isSuccess);
};

}; //namespace log
}; //namespace common
}; //namespace uxas

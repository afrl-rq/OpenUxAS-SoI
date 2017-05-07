// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_DATABASE_LOGGER_H
#define UXAS_COMMON_LOG_DATABASE_LOGGER_H

#include "UxAS_LoggerBase.h"
#include "UxAS_DatabaseLoggerHelper.h"

#include <memory>
#include <string>

namespace uxas
{
namespace common
{
namespace log
{

class DatabaseLogger : public LoggerBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("DatabaseLogger"); return (s_string); };

    static
    LoggerBase*
    create()
    {
        return new DatabaseLogger;
    };

    DatabaseLogger();

    ~DatabaseLogger();

private:

    static LoggerBase::CreationRegistrar<DatabaseLogger> s_registrar;

    // \brief Prevent copy construction
    DatabaseLogger(const DatabaseLogger&) = delete;

    // \brief Prevent copy assignment operation
    DatabaseLogger& operator=(const DatabaseLogger&) = delete;

public:

    bool
    configureDatabase(const std::string& createDatabase, const std::string& databaseTableName, const std::string& databaseTableColumnNames);
    
    bool
    openStream(std::string& logFilePath) override;

    bool
    closeStream() override;

    bool
    outputTextToStream(const std::string& text) override;

private:
    
    std::unique_ptr<DatabaseLoggerHelper> m_databaseLoggerHelper;

};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_LOG_DATABASE_LOGGER_H */

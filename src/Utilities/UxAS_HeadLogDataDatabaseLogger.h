// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_HEAD_LOG_DATA_DATABASE_LOGGER_H
#define UXAS_COMMON_LOG_HEAD_LOG_DATA_DATABASE_LOGGER_H

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

class HeadLogDataDatabaseLogger : public LoggerBase
{
public:

    static const std::string&
    s_defaultUxasMainHeadLogDataDatabaseLoggerName() { static std::string s_string("UxasMainHeadLogDataDatabaseLogger"); return (s_string); };

    static const std::string&
    s_typeName() { static std::string s_string("HeadLogDataDatabaseLogger"); return (s_string); };

    static
    LoggerBase*
    create()
    {
        return new HeadLogDataDatabaseLogger;
    };

    HeadLogDataDatabaseLogger();

    ~HeadLogDataDatabaseLogger();

private:

    static LoggerBase::CreationRegistrar<HeadLogDataDatabaseLogger> s_registrar;

    // \brief Prevent copy construction
    HeadLogDataDatabaseLogger(const HeadLogDataDatabaseLogger&) = delete;

    // \brief Prevent copy assignment operation
    HeadLogDataDatabaseLogger& operator=(const HeadLogDataDatabaseLogger&) = delete;

public:

    bool
    configure(const std::string& location, const bool isTimestamp = true, const bool isLogThreadId = true, const uint32_t updateLoggerCountLimit = 2000) override;

    bool
    openStream(std::string& logFilePath) override;

    bool
    closeStream() override;

    bool
    outputToStream(HeadLogData& headerAndData) override;

private:

    std::unique_ptr<DatabaseLoggerHelper> m_HeadLogDataDatabaseLoggerHelper;

};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_LOG_HEAD_LOG_DATA_DATABASE_LOGGER_H */

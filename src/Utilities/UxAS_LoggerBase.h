// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_LOGGER_BASE_H
#define UXAS_COMMON_LOG_LOGGER_BASE_H

#include "UxAS_LogSeverityLevel.h"
#include "UxAS_Time.h"

#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>

namespace uxas
{
namespace common
{
namespace log
{

/** \class HeadLogData
    \brief Data object for log header fields and data
 */
struct HeadLogData
{
    HeadLogData() : m_time_ms(0), m_threadID(""), m_severityLevelString(""), m_message("") { };
    int64_t m_time_ms;
    std::stringstream m_threadID;
    LogSeverityLevel m_severityLevel = LogSeverityLevel::UXASDEBUG;
    std::string m_severityLevelString;
    std::stringstream m_message;
};


class LoggerBase
{
public:

    /** \brief instantiates and returns a unique smart pointer to a logger.  */
    static
    std::unique_ptr<LoggerBase>
    instantiateLogger(const std::string& loggerType)
    {
        std::unique_ptr<LoggerBase> logger;
        auto it = registry().find(loggerType);
        LoggerBase* newLogger(it == registry().end() ? nullptr : (it->second)());
        logger.reset(newLogger);
        return (logger);
    };

protected:

    /** \brief type representing a pointer to a logger creation function.  */
    using loggerCreationFunctionPointer = LoggerBase* (*)();

    /** \brief static logger creation function implemented by deriving classes.  */
    static
    LoggerBase*
    create()
    {
        return (nullptr);
    };

    /** \brief registers logger type and the create() function of a deriving class.  */
    static
    void
    registerLoggerCreationFunctionPointer(const std::string& loggerType, loggerCreationFunctionPointer functionPointer)
    {
        registry()[loggerType] = functionPointer;
    };

    template <typename T>
    struct CreationRegistrar
    {
        explicit
        CreationRegistrar(const std::string& loggerType)
        {
            LoggerBase::registerLoggerCreationFunctionPointer(loggerType, &T::create);
        }
    };

private:

    static
    std::unordered_map<std::string, uxas::common::log::LoggerBase::loggerCreationFunctionPointer>&
    registry()
    {
        static std::unordered_map<std::string, uxas::common::log::LoggerBase::loggerCreationFunctionPointer> impl;
        return impl;
    }

public:

    static bool
    outputToStreamBasicFormat(std::ostream& oStream, const std::string& text, bool isLogThreadId, bool isTimeIsolatedLine)
    {
        oStream << "<MessageData UtcTimeSinceEpoch_ms=\"" << std::to_string(uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms());
        if (isTimeIsolatedLine)
        {
            if (isLogThreadId)
            {
                oStream << "\" ThreadId=\"" << std::this_thread::get_id() << "\"/>" << std::endl << "<!-- "  << text << " -->" << std::endl;
            }
            else
            {
                oStream << "\"/>"  << std::endl << "<!-- "  << text << " -->" << std::endl;
            }
        }
        else
        {
            if (isLogThreadId)
            {
                oStream << "\" ThreadId=\"" << std::this_thread::get_id() << "\"/>" << std::endl << "<!-- "  << text << " -->" << std::endl;
            }
            else
            {
                oStream << "\"/>"  << " <!-- " << text << " -->" << std::endl;
            }
        }
        return (true);
    };

    static bool
    outputToStreamBasicFormat(std::ostream& oStream, HeadLogData& headerAndData)
    {
        if (headerAndData.m_threadID.tellp() > 0) // is thread ID populated?
        {
            oStream << headerAndData.m_time_ms << ' ' << headerAndData.m_threadID.str() << headerAndData.m_severityLevelString<< headerAndData.m_message.str() << std::endl;
        }
        else
        {
            oStream << headerAndData.m_time_ms << headerAndData.m_severityLevelString << headerAndData.m_message.str() << std::endl;
        }
        return (true);
    };

    LoggerBase(std::string loggerType)
    : m_loggerType(loggerType) { };

    virtual
    ~LoggerBase() { };

private:

    // \brief Prevent copy construction
    LoggerBase(const LoggerBase&) = delete;

    // \brief Prevent copy assignment operation
    LoggerBase& operator=(const LoggerBase&) = delete;

public:

    virtual bool configure(const std::string& location, const bool isTimestamp = true, const bool isLogThreadId = false, const uint32_t updateLoggerCountLimit = 2000)
    {
        m_location = location;
        m_isTimestamp = isTimestamp;
        m_isLogThreadId = isLogThreadId;
        m_loggerStatementCountLimit = updateLoggerCountLimit;
        return(true);
    };

    virtual bool openStream(std::string& logFilePath) { return true; };

    virtual bool openStream() { std::string logFilePath; return(openStream(logFilePath)); };

    virtual bool closeStream() { return true; };

    virtual bool outputTextToStream(const std::string& text)
    {
        std::cout << "WARN: LoggerBase::outputTextToStream(string) is invalid method call" << std::endl;
        return false;
    };
    
    virtual bool outputTimeTextToStream(const std::string& text, bool isTimeIsolatedLine = true)
    {
        std::cout << "WARN: LoggerBase::outputTimeTextToStream is invalid method call" << std::endl;
        return false;
    };
    
    virtual bool outputToStream(HeadLogData& headerAndData)
    {
        std::cout << "WARN: LoggerBase::outputToStream(HeaderAndData) is invalid method call" << std::endl;
        return false;
    };
    
    LogSeverityLevel m_severityLevelThreshold = LogSeverityLevel::UXASDEBUG;
    
    std::string m_loggerType;

    std::string m_location;
    bool m_isTimestamp{true};
    bool m_isLogThreadId{false};
    uint32_t m_loggerStatementCountLimit{2000};

    std::string m_name;
    
};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_LOG_LOGGER_BASE_H */

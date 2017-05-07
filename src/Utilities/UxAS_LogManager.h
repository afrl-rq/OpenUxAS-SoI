// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_LOG_MANAGER_H
#define UXAS_COMMON_LOG_LOG_MANAGER_H

#include "UxAS_ConfigurationManager.h"
#include "UxAS_LoggerBase.h"
#include "UxAS_LogSeverityLevel.h"
#include "UxAS_Time.h"

#include "stdUniquePtr.h"

#include <algorithm>
#include <memory>
#include <string>
#include <sstream>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <cstdint>
#include <vector>

namespace uxas
{
namespace common
{
namespace log
{

/** \class LogManager
 * 
 * \par Description:
 * Singleton pattern
 * 
 * \n
 */
class LogManager
{
    friend uxas::common::ConfigurationManager;
    
private:

    static const std::string&
    debugString() { static std::string s_string(" DEBUG: "); return (s_string); };

    static const std::string&
    infoString() { static std::string s_string(" INFO:  "); return (s_string); };

    static const std::string&
    warningString() { static std::string s_string(" WARN:  "); return (s_string); };

    static const std::string&
    errorString() { static std::string s_string(" ERROR: "); return (s_string); };

public:

    static LogManager&
    getInstance();

    ~LogManager();

private:

    // \brief Prevent direct, public construction (singleton pattern)
    LogManager() { };

    // \brief Prevent copy construction
    LogManager(LogManager const&) = delete;

    // \brief Prevent copy assignment operation
    void operator=(LogManager const&) = delete;

public:

    bool
    addLogger(const std::string& name, const std::string& loggerType, LogSeverityLevel severityLevelThreshold,
              const std::string& configuration, std::string& logFilePath);

    void
    removeLoggersByLoggerType(const std::string& loggerType);

    void
    removeLoggersByName(const std::string& name);

    void
    removeLoggersByLoggerTypeAndName(const std::string& loggerType, const std::string& name);
        
    void
    setLoggersSeverityLevelByLoggerType(const std::string& loggerType, LogSeverityLevel severityLevelThreshold);

    void
    setLoggersSeverityLevelByName(const std::string& name, LogSeverityLevel severityLevelThreshold);

    void
    setLoggersSeverityLevelByLoggerTypeAndName(const std::string& loggerType, const std::string& name, LogSeverityLevel severityLevelThreshold);
        
    template<LogSeverityLevel logSeverity, typename...Args>
    void
    log(Args...args)
    {
        if (logSeverity >= m_severityLevelThreshold)
        {
            m_mutex.lock();
            switch (logSeverity)
            {
                case LogSeverityLevel::UXASDEBUG:
                    m_currentHeaderAndData->m_severityLevel = LogSeverityLevel::UXASDEBUG;
                    m_currentHeaderAndData->m_severityLevelString = debugString();
                    break;
                case LogSeverityLevel::UXASINFO:
                    m_currentHeaderAndData->m_severityLevel = LogSeverityLevel::UXASINFO;
                    m_currentHeaderAndData->m_severityLevelString = infoString();
                    break;
                case LogSeverityLevel::UXASWARNING:
                    m_currentHeaderAndData->m_severityLevel = LogSeverityLevel::UXASWARNING;
                    m_currentHeaderAndData->m_severityLevelString = warningString();
                    break;
                case LogSeverityLevel::UXASERROR:
                    m_currentHeaderAndData->m_severityLevel = LogSeverityLevel::UXASERROR;
                    m_currentHeaderAndData->m_severityLevelString = errorString();
                    break;
            };
            outputToLog(args...);
            m_mutex.unlock();
        }
    };

private:

    void
    removeLoggersByLoggerTypeAndNameImpl(const std::string& loggerType, const std::string& name, bool isCheckLoggerType, bool isCheckName);

    void
    setLoggerSeverityLevelByTypeAndNameImpl(const std::string& loggerType, const std::string& name, LogSeverityLevel severityLevelThreshold, bool isCheckLoggerType, bool isCheckName);
    
    template<typename First, typename...Rest>
    void
    outputToLog(First parm1, Rest...parm)
    {
        if (m_currentHeaderAndData->m_message.tellp() > 0)
        {
            m_currentHeaderAndData->m_message << parm1;
        }
        else
        {
            m_currentHeaderAndData->m_time_ms = uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms();
            m_currentHeaderAndData->m_message << parm1;
            if (m_isLoggingThreadId)
            {
                m_currentHeaderAndData->m_threadID << std::this_thread::get_id();
            }
        }

        // recursive processing of tokens
        outputToLog(parm...);
    };

    void
    outputToLog()
    {
        outputToLoggers(std::move(m_currentHeaderAndData));
        m_currentHeaderAndData = uxas::stduxas::make_unique<uxas::common::log::HeadLogData>();
    };

    void
    outputToLoggers(std::unique_ptr<uxas::common::log::HeadLogData> headerAndData)
    {
        // iterate thru loggers, conditionally output log string
        // based on log severity threshold
        for (auto& loggerIt : m_loggers)
        {
            if (loggerIt && loggerIt->m_severityLevelThreshold <= headerAndData->m_severityLevel)
            {
                loggerIt->outputToStream(*headerAndData);
            }
        }
    };

    std::string
    getDate();

    static std::unique_ptr<LogManager> s_instance;

    bool m_isLoggingThreadId;

    std::mutex m_mutex;
    std::vector<std::unique_ptr<uxas::common::log::LoggerBase>> m_loggers;

    LogSeverityLevel m_severityLevelThreshold = LogSeverityLevel::UXASDEBUG;
    std::unique_ptr<uxas::common::log::HeadLogData> m_currentHeaderAndData;
};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_LOG_LOG_MANAGER_H */

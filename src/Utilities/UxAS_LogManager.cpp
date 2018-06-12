// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_LogManager.h"
#include "UxAS_ConsoleLogger.h"
#include "UxAS_DatabaseLogger.h"
#include "UxAS_FileLogger.h"
#include "UxAS_HeadLogDataDatabaseLogger.h"

#include "stdUniquePtr.h"

#include <iostream>

#define LOG_MANAGER_LOCAL_LOG_MESSAGE(message) std::cout << message << std::endl; std::cout.flush();

namespace uxas
{
namespace common
{
namespace log
{

std::unique_ptr<LogManager> LogManager::s_instance = nullptr;

LogManager&
LogManager::getInstance()
{
    // first time/one time creation
    if (LogManager::s_instance == nullptr)
    {
        // force initialization of classes and their static class members
        // <editor-fold defaultstate="collapsed" desc="trigger static LoggerBase subclass initialization">
        {
            auto logger = uxas::stduxas::make_unique<uxas::common::log::ConsoleLogger>();
        }
        {
            auto logger = uxas::stduxas::make_unique<uxas::common::log::DatabaseLogger>();
        }
        {
            auto logger = uxas::stduxas::make_unique<uxas::common::log::FileLogger>();
        }
        {
            auto logger = uxas::stduxas::make_unique<uxas::common::log::HeadLogDataDatabaseLogger>();
        }
        // </editor-fold>

        s_instance.reset(new LogManager);
        s_instance->m_isLoggingThreadId = uxas::common::ConfigurationManager::getInstance().getIsLoggingThreadId();
        s_instance->m_currentHeaderAndData = uxas::stduxas::make_unique<uxas::common::log::HeadLogData>();
    }

    return *s_instance;
};

LogManager::~LogManager()
{
    for (auto& loggerIt : m_loggers)
    {
        if (loggerIt)
        {
            loggerIt->closeStream();
        }
    }
};

bool
LogManager::addLogger(const std::string& name, const std::string& loggerType, LogSeverityLevel severityLevelThreshold,
                      const std::string& configuration, std::string& logFilePath)
{
    // attempt to instantiate and add requested logger
    bool isSuccess{false};
    std::unique_ptr<LoggerBase> newLogger = LoggerBase::instantiateLogger(loggerType);
    if (newLogger)
    {
        try
        {
            if (newLogger->configure(configuration, uxas::common::ConfigurationManager::getIsDataTimeStamp(), uxas::common::ConfigurationManager::getIsLoggingThreadId()))
            {
                if (newLogger->openStream(logFilePath))
                {
                    newLogger->m_severityLevelThreshold = severityLevelThreshold;
                    newLogger->m_name = name;
                    m_mutex.lock();
                    m_loggers.emplace_back(std::move(newLogger));
                    m_mutex.unlock();
                    uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASINFO>("LogManager successfully opened stream for logger [", loggerType, "] having name [", name, "] and configuration [", configuration, "]");
                    isSuccess = true;
                }
                else
                {
                    LOG_MANAGER_LOCAL_LOG_MESSAGE("ERROR LogManager failed to open stream for logger type [" << loggerType << "] having name [" << name << "] and configuration [" << configuration <<"]")
                }
            }
            else
            {
                LOG_MANAGER_LOCAL_LOG_MESSAGE("ERROR LogManager failed to configure logger for logger type [" << loggerType << "] having name [" << name << "] and configuration [" << configuration <<"]")
            }
        }
        catch (std::exception& ex)
        {
            LOG_MANAGER_LOCAL_LOG_MESSAGE("ERROR LogManager failed to instantiate logger for logger type [" << loggerType << "] having name [" << name << "] and configuration [" << configuration << "] EXCEPTION: " << ex.what())
        }
    }
    else
    {
        LOG_MANAGER_LOCAL_LOG_MESSAGE("ERROR LogManager failed to instantiate logger for logger type [" << loggerType << "] having name [" << name << "] and configuration [" << configuration << "]")
    }
    return (isSuccess);
};

void
LogManager::removeLoggersByLoggerType(const std::string& loggerType)
{
    removeLoggersByLoggerTypeAndNameImpl(loggerType, "", true, false);
};

void
LogManager::removeLoggersByName(const std::string& name)
{
    removeLoggersByLoggerTypeAndNameImpl("", name, false, true);
};

void
LogManager::removeLoggersByLoggerTypeAndName(const std::string& loggerType, const std::string& name)
{
    removeLoggersByLoggerTypeAndNameImpl(loggerType, name, true, true);
}

void
LogManager::setLoggersSeverityLevelByLoggerType(const std::string& loggerType, LogSeverityLevel severityLevelThreshold)
{
    setLoggerSeverityLevelByTypeAndNameImpl(loggerType, "", severityLevelThreshold, true, false);
};

void
LogManager::setLoggersSeverityLevelByName(const std::string& name, LogSeverityLevel severityLevelThreshold)
{
    setLoggerSeverityLevelByTypeAndNameImpl("", name, severityLevelThreshold, false, true);
};

void
LogManager::setLoggersSeverityLevelByLoggerTypeAndName(const std::string& loggerType, const std::string& name, LogSeverityLevel severityLevelThreshold)
{
    setLoggerSeverityLevelByTypeAndNameImpl(loggerType, name, severityLevelThreshold, true, true);
}

void
LogManager::removeLoggersByLoggerTypeAndNameImpl(const std::string& loggerType, const std::string& name, bool isCheckLoggerType, bool isCheckName)
{
    m_mutex.lock();
    // iterate thru loggers, close output stream and remove loggers
    for (auto loggerIt = m_loggers.begin(); loggerIt != m_loggers.end();)
    {
        if (*loggerIt)
        {
            if (isCheckLoggerType && isCheckName)
            {
                if ((*loggerIt)->m_loggerType == loggerType && (*loggerIt)->m_name == name)
                {
                    (*loggerIt)->closeStream();
                    loggerIt = m_loggers.erase(loggerIt);
                }
                else
                {
                    ++loggerIt;
                }
            }
            else if (isCheckLoggerType)
            {
                if ((*loggerIt)->m_loggerType == loggerType)
                {
                    (*loggerIt)->closeStream();
                    loggerIt = m_loggers.erase(loggerIt);
                }
                else
                {
                    ++loggerIt;
                }
            }
            else if (isCheckName)
            {
                if ((*loggerIt)->m_name == name)
                {
                    (*loggerIt)->closeStream();
                    loggerIt = m_loggers.erase(loggerIt);
                }
                else
                {
                    ++loggerIt;
                }
            }
        }
        else
        {
            LOG_MANAGER_LOCAL_LOG_MESSAGE("WARNING LogManager removing logger having logger type [" << (*loggerIt)->m_loggerType << "] having name [" << (*loggerIt)->m_name << "]")
            loggerIt = m_loggers.erase(loggerIt);
        }
    }
    m_mutex.unlock();
};

void
LogManager::setLoggerSeverityLevelByTypeAndNameImpl(const std::string& loggerType, const std::string& name, LogSeverityLevel severityLevelThreshold, bool isCheckLoggerType, bool isCheckName)
{
    m_mutex.lock();
    // iterate thru loggers, update log severity level
    for (auto loggerIt = m_loggers.begin(); loggerIt != m_loggers.end();)
    {
        if (*loggerIt)
        {
            if (isCheckLoggerType && isCheckName)
            {
                if ((*loggerIt)->m_loggerType == loggerType && (*loggerIt)->m_name == name)
                {
                    (*loggerIt)->m_severityLevelThreshold = severityLevelThreshold;
                }
            }
            else if (isCheckLoggerType)
            {
                if ((*loggerIt)->m_loggerType == loggerType)
                {
                    (*loggerIt)->m_severityLevelThreshold = severityLevelThreshold;
                }
            }
            else if (isCheckName)
            {
                if ((*loggerIt)->m_name == name)
                {
                    (*loggerIt)->m_severityLevelThreshold = severityLevelThreshold;
                }
            }
            ++loggerIt;
        }
        else
        {
            LOG_MANAGER_LOCAL_LOG_MESSAGE("WARNING LogManager removing logger having logger type [" << (*loggerIt)->m_loggerType << "] having name [" << (*loggerIt)->m_name << "]")
            loggerIt = m_loggers.erase(loggerIt);
        }
    }
    m_mutex.unlock();
};

std::string
LogManager::getDate()
{
    time_t raw_time;
    time(& raw_time);
    
#ifdef _WIN32
    char str_buf[100];
    ctime_s(str_buf, 100, &raw_time);
    std::string time_str(str_buf);
#else
    std::string time_str(ctime(&raw_time));
#endif
    //without the newline character
    return time_str.substr(0, time_str.size() - 1);
};

}; //namespace log
}; //namespace common
}; //namespace uxas
        
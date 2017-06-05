// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_LOG_MANAGER_DEFAULT_INITIALIZER_H
#define UXAS_COMMON_LOG_LOG_MANAGER_DEFAULT_INITIALIZER_H

#include "UxAS_ConfigurationManager.h"
#include "UxAS_ConsoleLogger.h"
#include "UxAS_FileLogger.h"
#include "UxAS_HeadLogDataDatabaseLogger.h"
#include "UxAS_Log.h"
#include "UxAS_LoggerBase.h"
#include "UxAS_LogManager.h"
#include "UxAS_LogSeverityLevel.h"

#include "FileSystemUtilities.h"

#include <string>

namespace uxas
{
namespace common
{
namespace log
{

/** \class LogManagerDefaultInitializer
 * 
 * \par Description:
 * UxAS default initializer of LogManager.
 * 
 * \n
 */
class LogManagerDefaultInitializer
{
public:

    static bool
    initializeConsoleLogger()
    {
        //uxas::common::StringConstant::SerialTimeout_ms()
        std::string logFilePath;
        return (uxas::common::log::LogManager::getInstance().addLogger(uxas::common::log::ConsoleLogger::s_defaultUxasConsoleLoggerName(), 
                                                                       uxas::common::log::ConsoleLogger::s_typeName(), 
                                                                       uxas::common::log::LogSeverityLevel::UXASWARNING, "",logFilePath));
    };

    static bool
    initializeMainDatabaseLogger(const bool isTimestampDir = false)
    {
        std::string logDir = "./log/" + 
                (isTimestampDir ? (std::to_string(uxas::common::ConfigurationManager::getInstance().getEntityStartTimeSinceEpoch_ms()) + "/") : "");
        return(initializeMainDatabaseLogger(logDir));
    }
    
    static bool
    initializeMainDatabaseLogger(const std::string& logDir)
    {
        std::stringstream errors;
        bool isCreateDirSuccess{false};
        try
        {
            isCreateDirSuccess = uxas::common::utilities::c_FileSystemUtilities::bCreateDirectory(logDir, errors);
        }
        catch (std::exception& ex)
        {
            UXAS_LOG_ERROR("LogManagerDefaultInitializer::initializeMainFileLogger EXCEPTION: ", ex.what());
        }
        
        if (isCreateDirSuccess)
        {
            UXAS_LOG_INFORM("LogManagerDefaultInitializer::initializeMainDatabaseLogger created log directory ", logDir);
            std::string logFilePath;    //not used??
            return (uxas::common::log::LogManager::getInstance().addLogger(uxas::common::log::HeadLogDataDatabaseLogger::s_defaultUxasMainHeadLogDataDatabaseLoggerName(),
                                                                           uxas::common::log::HeadLogDataDatabaseLogger::s_typeName(),
                                                                           uxas::common::log::LogSeverityLevel::UXASINFO, logDir + "log",logFilePath));
        }
        else
        {
            UXAS_LOG_ERROR("LogManagerDefaultInitializer::initializeMainDatabaseLogger failed to create log directory ", logDir);
            return (false);
        }
    };
    
    static bool
    initializeMainFileLogger(const bool isTimestampDir = false)
    {
        std::string logDir = "./log/" + 
                (isTimestampDir ? (std::to_string(uxas::common::ConfigurationManager::getInstance().getEntityStartTimeSinceEpoch_ms()) + "/") : "");
        std::string logFilePath; //not used
        return(initializeMainFileLogger(logDir,logFilePath));
    }
    
    static bool
    initializeMainFileLogger(const std::string& logDir,std::string& logFilePath)
    {
        std::stringstream errors;
        bool isCreateDirSuccess{false};
        try
        {
            isCreateDirSuccess = uxas::common::utilities::c_FileSystemUtilities::bCreateDirectory(logDir, errors);
        }
        catch (std::exception& ex)
        {
            UXAS_LOG_ERROR("LogManagerDefaultInitializer::initializeMainFileLogger EXCEPTION: ", ex.what());
        }
        
        if (isCreateDirSuccess)
        {
            UXAS_LOG_INFORM("LogManagerDefaultInitializer::initializeMainFileLogger created log directory ", logDir);
            return (uxas::common::log::LogManager::getInstance().addLogger(uxas::common::log::FileLogger::s_defaultUxasMainFileLoggerName(),
                                                                           uxas::common::log::FileLogger::s_typeName(),
                                                                           uxas::common::log::LogSeverityLevel::UXASDEBUG, logDir + "log",
                                                                           logFilePath));
        }
        else
        {
            UXAS_LOG_ERROR("LogManagerDefaultInitializer::initializeMainFileLogger failed to create log directory ", logDir);
            return (false);
        }
    };
    
    LogManagerDefaultInitializer();

    ~LogManagerDefaultInitializer();

private:

    // \brief Prevent copy construction
    LogManagerDefaultInitializer(LogManagerDefaultInitializer const&) = delete;

    // \brief Prevent copy assignment operation
    void operator=(LogManagerDefaultInitializer const&) = delete;

public:

};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_LOG_LOG_MANAGER_DEFAULT_INITIALIZER_H */

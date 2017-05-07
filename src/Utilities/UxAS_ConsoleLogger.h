// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_CONSOLE_LOGGER_H
#define UXAS_COMMON_LOG_CONSOLE_LOGGER_H

#include "UxAS_LoggerBase.h"

#include <string>

namespace uxas
{
namespace common
{
namespace log
{

class ConsoleLogger : public LoggerBase
{
public:

    static const std::string&
    s_defaultUxasConsoleLoggerName() { static std::string s_string("UxasConsoleLogger"); return (s_string); };

    static const std::string&
    s_typeName() { static std::string s_string("ConsoleLogger"); return (s_string); };

    static
    LoggerBase*
    create()
    {
        return new ConsoleLogger;
    };

    ConsoleLogger();

    ~ConsoleLogger() { };

private:

    static LoggerBase::CreationRegistrar<ConsoleLogger> s_registrar;

    // \brief Prevent copy construction
    ConsoleLogger(const ConsoleLogger&) = delete;

    // \brief Prevent copy assignment operation
    ConsoleLogger& operator=(const ConsoleLogger&) = delete;

public:

    bool
    outputTextToStream(const std::string& text) override;
    
    bool    
    outputTimeTextToStream(const std::string& text, bool isTimeIsolatedLine) override;

    bool
    outputToStream(HeadLogData& headerAndData) override;

};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_LOG_CONSOLE_LOGGER_H */

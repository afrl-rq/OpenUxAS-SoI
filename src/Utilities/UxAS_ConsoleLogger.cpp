// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_ConsoleLogger.h"

#include <iostream>

namespace uxas
{
namespace common
{
namespace log
{

ConsoleLogger::LoggerBase::CreationRegistrar<ConsoleLogger> ConsoleLogger::s_registrar(s_typeName());

ConsoleLogger::ConsoleLogger()
: LoggerBase(s_typeName())
{
};

bool
ConsoleLogger::outputTextToStream(const std::string& text)
{
    std::cout << text << std::endl;
    return (true);
};

bool
ConsoleLogger::outputTimeTextToStream(const std::string& text, bool isTimeIsolatedLine)
{
    return (outputToStreamBasicFormat(std::cout, text, m_isLogThreadId, isTimeIsolatedLine));
};

bool
ConsoleLogger::outputToStream(HeadLogData& headerAndData)
{
    return (outputToStreamBasicFormat(std::cout, headerAndData));
};

}; //namespace log
}; //namespace common
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_FILE_LOGGER_H
#define UXAS_COMMON_LOG_FILE_LOGGER_H

#include "UxAS_LoggerBase.h"

#include <fstream>
#include <memory>
#include <string>

namespace uxas
{
namespace common
{
namespace log
{

class FileLogger : public LoggerBase
{
public:

    static const std::string&
    s_defaultUxasMainFileLoggerName() { static std::string s_string("UxasMainFileLogger"); return (s_string); };

    static const std::string&
    s_typeName() { static std::string s_string("FileLogger"); return (s_string); };

    static
    LoggerBase*
    create()
    {
        return new FileLogger;
    };

    FileLogger();

    ~FileLogger();

private:

    static LoggerBase::CreationRegistrar<FileLogger> s_registrar;

    // \brief Prevent copy construction
    FileLogger(const FileLogger&) = delete;

    // \brief Prevent copy assignment operation
    FileLogger& operator=(const FileLogger&) = delete;

public:

    bool
    openStream(std::string& logFilePath) override;

    bool
    closeStream() override;

    bool
    outputTextToStream(const std::string& text) override;
    
    bool
    outputTimeTextToStream(const std::string& text, bool isTimeIsolatedLine = true) override;

    bool
    outputToStream(HeadLogData& headerAndData) override;

private:

    void
    closeAndOpenStream();

    std::string m_logFilePath;
    std::string m_logFilePathOld;
    std::string m_logFilePathCloseFailed;
    uint32_t m_logFileCount{0};
    uint32_t m_logFileStatementCount{1};
    uint32_t m_logFileCloseFailureCount{0};
    std::unique_ptr<std::ofstream> m_outputFileStream;

};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_LOG_FILE_LOGGER_H */

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_FileLogger.h"

#include "UxAS_Time.h"

#include "stdUniquePtr.h"

namespace uxas
{
namespace common
{
namespace log
{

FileLogger::LoggerBase::CreationRegistrar<FileLogger> FileLogger::s_registrar(s_typeName());

FileLogger::FileLogger()
: LoggerBase(s_typeName())
{
    m_outputFileStream = uxas::stduxas::make_unique<std::ofstream>();
};

FileLogger::~FileLogger()
{
    if (m_outputFileStream)
    {
        closeStream();
    }
};

bool
FileLogger::openStream(std::string& logFilePath)
{
    bool isSuccess{false};
    m_logFilePathOld = m_logFilePath;
    m_logFilePath = m_location + '_' + std::to_string(++m_logFileCount) 
            + (m_isTimestamp ? ('_' + std::to_string(uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms())) : "");
    logFilePath = m_logFilePath;
    m_outputFileStream->open(m_logFilePath.c_str(), std::ios_base::binary | std::ios_base::out);
    isSuccess = m_outputFileStream->is_open();
    return (isSuccess);
};

bool
FileLogger::closeStream()
{
    bool isSuccess{true};
    if (m_outputFileStream)
    {
        m_outputFileStream->flush();
        m_outputFileStream->close();
        if (!m_logFilePathOld.empty() && m_outputFileStream->fail())
        {
            isSuccess = false;
            m_logFilePathCloseFailed = m_logFilePathOld;
            m_logFileCloseFailureCount++;
            std::cout << "WARN: FileLogger failed to close log file [" << m_logFilePathCloseFailed << "]" << std::endl;
            std::cout << "WARN: FileLogger close log file failure count [" << m_logFileCloseFailureCount << "]" << std::endl;
        }
    }
    return (isSuccess);
};

bool
FileLogger::outputTextToStream(const std::string& text)
{
    (*m_outputFileStream) << text << std::endl;
    m_logFileStatementCount++;
    closeAndOpenStream();
    return (true);
};

bool
FileLogger::outputTimeTextToStream(const std::string& text, bool isTimeIsolatedLine)
{
    outputToStreamBasicFormat(*m_outputFileStream, text, m_isLogThreadId, isTimeIsolatedLine);
    m_logFileStatementCount++;
    closeAndOpenStream();
    return (true);
};

bool
FileLogger::outputToStream(HeadLogData& headerAndData)
{
    outputToStreamBasicFormat(*m_outputFileStream, headerAndData);
    m_logFileStatementCount++;
    closeAndOpenStream();
    return (true);
};

void
FileLogger::closeAndOpenStream()
{
    if (m_logFileStatementCount > m_loggerStatementCountLimit)
    {
        if (!closeStream())
        {
            (*m_outputFileStream) << "FileLogger::closeAndOpenStream WARN: FileLogger failed to close log file [" << m_logFilePathOld << "]" << std::endl;
        }
        std::string logFilePath;
        if (!openStream(logFilePath))
        {
            (*m_outputFileStream) << "FileLogger::closeAndOpenStream WARN: FileLogger failed to open log file" << std::endl;
        }
        m_logFileStatementCount = 1;
        if (!m_logFilePathOld.empty() && m_logFileCloseFailureCount > 0)
        {
            if (m_logFilePathCloseFailed.size() > 0)
            {
                (*m_outputFileStream) << "FileLogger::closeAndOpenStream WARN: FileLogger failed to close log file [" << m_logFilePathCloseFailed << "]" << std::endl;
                m_logFilePathCloseFailed = "";
            }
            (*m_outputFileStream) << "FileLogger::closeAndOpenStream WARN: FileLogger close log file failure count [" << m_logFileCloseFailureCount << "]" << std::endl;
        }
    }
};

}; //namespace log
}; //namespace common
}; //namespace uxas

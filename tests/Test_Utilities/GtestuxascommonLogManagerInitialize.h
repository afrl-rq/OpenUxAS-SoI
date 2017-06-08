#include "gtest/gtest.h"

#include "UxAS_Log.h"
#include "UxAS_LogManagerDefaultInitializer.h"

#define GTEST_LOG_MANAGER_INITIALIZE_MESSAGE(message) std::cout << message << std::endl; std::cout.flush();

static bool isCalledGtestuxascommonLogManagerInitialize = false;

void
gtestuxascommonLogManagerInitialize(const std::string& logPath,bool isReInitialize=false)
{
    if(isReInitialize)
    {
        isCalledGtestuxascommonLogManagerInitialize = false;
    }
    GTEST_LOG_MANAGER_INITIALIZE_MESSAGE("START GtestuxascommonLogManagerInitialize");
    GTEST_LOG_MANAGER_INITIALIZE_MESSAGE("isCalledGtestuxascommonLogManagerInitialize=" << isCalledGtestuxascommonLogManagerInitialize);
    if (isCalledGtestuxascommonLogManagerInitialize)
    {
        UXAS_LOG_INFORM("START GtestuxascommonLogManagerInitialize");
        UXAS_LOG_INFORM("isCalledGtestuxascommonLogManagerInitialize=", isCalledGtestuxascommonLogManagerInitialize);
    }
    else
    {
        isCalledGtestuxascommonLogManagerInitialize = true;
        ASSERT_TRUE(uxas::common::log::LogManagerDefaultInitializer::initializeConsoleLogger() ? true : false);
        UXAS_LOG_INFORM("Console logger initialized");
        std::string logFilePath;
        ASSERT_TRUE(uxas::common::log::LogManagerDefaultInitializer::initializeMainFileLogger(logPath,logFilePath) ? true : false);
        UXAS_LOG_INFORM("Main file logger initialized");
    }
    UXAS_LOG_INFORM("END GtestuxascommonLogManagerInitialize");
};

void
gtestuxascommonLogManagerInitialize()
{
    std::string logPath = "./log/";
    
    gtestuxascommonLogManagerInitialize(logPath);
};


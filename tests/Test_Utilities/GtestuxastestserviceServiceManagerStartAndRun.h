#include "gtest/gtest.h"

#include "GtestuxascommonLogManagerInitialize.h"
#include "ServiceManager.h"
#include "MessageLoggerDataService.h"
#include "LmcpObjectNetworkServer.h"
#include "ZeroMqFabric.h"
#include "avtas/lmcp/Object.h"
#include "avtas/lmcp/LmcpXMLReader.h"

#include "UxAS_ConfigurationManager.h"
#include "UxAS_Log.h"
#include "UxAS_LogManagerDefaultInitializer.h"

#include <SQLiteCpp/Database.h>
#include <SQLiteCpp/SQLiteCpp.h>
#include <vector>

#include "stdUniquePtr.h"

static bool isCalledgtestuxastestserviceServiceManagerStartAndRun = false;

void
gtestuxastestserviceServiceManagerStartAndRun(uint32_t duration_s);

void
gtestuxastestserviceServiceManagerStartAndRun(uint32_t duration_s, std::string baseCfgXmlPath);

void
gtestuxastestserviceServiceManagerStartAndRun(uint32_t duration_s, std::string baseCfgXmlPath, std::string outputPath, std::string& logFilePath);

void
gtestuxastestserviceServiceManagerStartAndRun(uint32_t duration_s)
{
    std::string logFilePath;
    gtestuxastestserviceServiceManagerStartAndRun(duration_s, "", "", logFilePath);
};

void
gtestuxastestserviceServiceManagerStartAndRun(uint32_t duration_s, std::string baseCfgXmlPath)
{
    std::string logFilePath;
    gtestuxastestserviceServiceManagerStartAndRun(duration_s, baseCfgXmlPath, "", logFilePath);
};

void
gtestuxastestserviceServiceManagerStartAndRun(uint32_t duration_s, std::string baseCfgXmlPath, std::string outputPath, std::string& logFilePath,bool isReset)
{
    if(isReset)
    {
        isCalledgtestuxastestserviceServiceManagerStartAndRun = false;
    }
    gtestuxastestserviceServiceManagerStartAndRun(duration_s,baseCfgXmlPath,outputPath,logFilePath);
}
void
gtestuxastestserviceServiceManagerStartAndRun(uint32_t duration_s, std::string baseCfgXmlPath, std::string outputPath, std::string& logFilePath)
{
    std::string logPath = outputPath + "log/";
    gtestuxascommonLogManagerInitialize(logPath);
    UXAS_LOG_INFORM("START gtestuxastestserviceServiceManagerStartAndRun");
    UXAS_LOG_INFORM("isCalledgtestuxastestserviceServiceManagerStartAndRun=", isCalledgtestuxastestserviceServiceManagerStartAndRun);
    UXAS_LOG_INFORM("duration_s=", duration_s);

    if (!isCalledgtestuxastestserviceServiceManagerStartAndRun)
    {
        isCalledgtestuxastestserviceServiceManagerStartAndRun = true;

        uxas::common::ConfigurationManager::s_rootDataWorkDirectory = outputPath + "SavedData/";

        UXAS_LOG_INFORM("Base cfg XML path parameter is: ", baseCfgXmlPath);
        ASSERT_TRUE((baseCfgXmlPath.empty() ?
                    uxas::common::ConfigurationManager::getInstance().loadBaseXmlFile() :
                    uxas::common::ConfigurationManager::getInstance().loadBaseXmlFile(baseCfgXmlPath)) ? true : false);

        std::unique_ptr<uxas::communications::LmcpObjectNetworkServer> networkServer = uxas::stduxas::make_unique<uxas::communications::LmcpObjectNetworkServer>();
        ASSERT_TRUE(networkServer ? true : false);
        UXAS_LOG_INFORM("Created network server");
        ASSERT_TRUE(networkServer->configure() ? true : false);
        UXAS_LOG_INFORM("Configured network server");
        ASSERT_TRUE(networkServer->initializeAndStart() ? true : false);
        UXAS_LOG_INFORM("Initialized and started network server");

        ASSERT_TRUE(uxas::service::ServiceManager::getInstance().configureServiceManager() ? true : false);
        UXAS_LOG_INFORM("Configured service manager");
        ASSERT_TRUE(uxas::service::ServiceManager::getInstance().initializeAndStartService() ? true : false);
        UXAS_LOG_INFORM("Initialized and started service manager");
        UXAS_LOG_INFORM("Retrieving Message Log Path");
        for (auto& service : uxas::service::ServiceManager::getInstance().getServicesById())
        {
            if (service.second->m_serviceType == std::string("MessageLoggerDataService"))
            {
                auto messageLoggerDataService = static_cast<uxas::service::data::MessageLoggerDataService*> (service.second.get());
                logFilePath = messageLoggerDataService->m_logFilePath;
            }
        }
        UXAS_LOG_INFORM("Started Timed Run");
        uxas::service::ServiceManager::getInstance().runUntil(duration_s);
        UXAS_LOG_INFORM("Finished Timed Run");
        uxas::service::ServiceManager::getInstance().destroyServiceManager();
        networkServer->terminate();
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        networkServer.reset();
        //uxas::communications::transport::ZeroMqFabric::getInstance().~ZeroMqFabric();
        uxas::communications::transport::ZeroMqFabric::Destroy();
    }
    UXAS_LOG_INFORM("END gtestuxastestserviceServiceManagerStartAndRun");
};

int32_t CountMessagesInLogDb(const std::string& logFilePath, const std::string& messageType)
{
    int32_t messageCount{-1};

    std::ifstream dbFile(logFilePath);
    if (dbFile.is_open())
    {
        // file is there, now reopen in sqlite
        dbFile.close();
        auto m_db = uxas::stduxas::make_unique<SQLite::Database>(logFilePath, SQLITE_OPEN_READWRITE);
        std::string sqlStmt = "SELECT descriptor FROM msg WHERE descriptor = \"" + messageType + "\"";
        SQLite::Statement selectStatements(*(m_db.get()), sqlStmt);
        messageCount = 0;
        while (selectStatements.executeStep())
        {
            //std::cout << "selectStatements.getColumn(0).getInt64()[" << selectStatements.getColumn(0).operator const std::string() << "]" << std::endl;
            messageCount++;
        }
        std::cout << "*** message[" << messageType << "] messageCount[" << messageCount << "]" << std::endl;
    }
    return (messageCount);
}

void ReportMessagesInLogDb(const std::string& logFilePath, const std::string& messageType, std::vector< std::shared_ptr<avtas::lmcp::Object> >& messages)
{
    std::ifstream dbFile(logFilePath);
    if (dbFile.is_open())
    {
        // file is there, now reopen in sqlite
        dbFile.close();
        auto m_db = uxas::stduxas::make_unique<SQLite::Database>(logFilePath, SQLITE_OPEN_READWRITE);
        std::string sqlStmt = "SELECT descriptor, xml FROM msg WHERE descriptor = \"" + messageType + "\"";
        SQLite::Statement selectStatements(*(m_db.get()), sqlStmt);
        while (selectStatements.executeStep())
        {
            auto obj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(selectStatements.getColumn(1)));
            if(obj)
                messages.push_back(obj);
        }
    }
}


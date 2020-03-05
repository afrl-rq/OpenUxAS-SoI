// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_ConfigurationManager.h"

#if defined(USE_GEO_LIBS)
#include "GroundHeight.h"   // utility function that needs dted configuration file names form the cfg file
#endif

#include "UxAS_ConsoleLogger.h"
#include "UxAS_HeadLogDataDatabaseLogger.h"
#include "UxAS_FileLogger.h"
#include "UxAS_Log.h"
#include "Constants/UxAS_String.h"
#include "UxAS_Time.h"

#include <cstring>
#include <fstream>
#include <string>
#include <sstream>
#include <unordered_map>
#include <set>

#if (defined(__APPLE__) && defined(__MACH__))
#define OSX
#endif

#if (defined(OSX) || defined(_WIN32))
#include <unordered_set>
#else
#include <bits/unordered_set.h>
#endif

namespace uxas
{
namespace common
{

bool ConfigurationManager::s_isZeroMqMultipartMessage{false};
uint32_t ConfigurationManager::s_serialPortWaitTime_ms = 50;
int32_t ConfigurationManager::s_zeroMqReceiveSocketPollWaitTime_ms = 1;
//int32_t ConfigurationManager::s_zeroMqReceiveSocketPollWaitTime_ms = 0;

int64_t ConfigurationManager::s_entityStartTimeSinceEpoch_ms = 0;
uint32_t ConfigurationManager::s_startDelay_ms = 0;
uint32_t ConfigurationManager::s_runDuration_s = UINT32_MAX;
bool ConfigurationManager::s_isLoggingThreadId{false};
bool ConfigurationManager::s_isDataTimestamp{true};

uint32_t ConfigurationManager::s_entityId = 0;
std::string ConfigurationManager::s_entityType{""};

std::string ConfigurationManager::s_rootDataInDirectory{"./datain/"};
std::string ConfigurationManager::s_rootDataRefDirectory{"./dataref/"};
std::string ConfigurationManager::s_rootDataWorkDirectory{"./datawork/"};

std::unique_ptr<ConfigurationManager> ConfigurationManager::s_instance = nullptr;

ConfigurationManager&
ConfigurationManager::getInstance()
{
    // first time/one time creation
    if (ConfigurationManager::s_instance == nullptr)
    {
        s_instance.reset(new ConfigurationManager);
        s_entityStartTimeSinceEpoch_ms = Time::getInstance().getUtcTimeSinceEpoch_ms();
    }

    return *s_instance;
};

bool
ConfigurationManager::loadBaseXmlFile(const std::string& xmlFilePath)
{
    return loadXml(xmlFilePath, true, true, false);
};

bool
ConfigurationManager::loadBaseXmlString(const std::string& xmlString)
{
    return loadXml(xmlString, false, true, false);
};

void
ConfigurationManager::unloadBaseXml()
{
    m_baseXmlDoc.reset();
    m_isBaseXmlDocLoaded = false;
    m_enabledBridgesXmlDoc.reset();
    m_isEnabledBridgesXmlDocBuilt = false;
    m_enabledServicesXmlDoc.reset();
    m_isEnabledServicesXmlDocBuilt = false;
};

void
ConfigurationManager::unloadXml()
{
    m_baseXmlDoc.reset();
    m_isBaseXmlDocLoaded = false;
    m_enabledBridgesXmlDoc.reset();
    m_isEnabledBridgesXmlDocBuilt = false;
    m_enabledServicesXmlDoc.reset();
    m_isEnabledServicesXmlDocBuilt = false;
};

bool
ConfigurationManager::loadXml(const std::string& xml, bool isFile, bool isBaseXml, bool isSetEntityPptys)
{
    bool isSuccess{false};
    pugi::xml_parse_result xmlParseSuccess;
    if (isBaseXml)
    {
        if (m_isBaseXmlDocLoaded)
        {
            m_baseXmlDoc.reset();
            m_isBaseXmlDocLoaded = false;
            m_isEnabledBridgesXmlDocBuilt = false;
            m_isEnabledServicesXmlDocBuilt = false;
        }
        if (isFile)
        {
            std::ifstream xmlInputStream(xml);
            xmlParseSuccess = m_baseXmlDoc.load(xmlInputStream);
        }
        else
        {
            xmlParseSuccess = m_baseXmlDoc.load(xml.c_str());
        }
        m_isBaseXmlDocLoaded = true;
#ifdef DEBUG_VERBOSE_LOGGING_ENABLED
        std::stringstream baseXmlNd{""};
        m_baseXmlDoc.print(baseXmlNd);
        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::loadXml loaded base XML ", baseXmlNd.str());
#endif
    }

    if (xmlParseSuccess)
    {
        if (setEntityValuesFromXmlNode(m_baseXmlDoc.root()))
        {
            isSuccess = true;
        }
        else
        {
            isSuccess = false;
        }
        loadUtilityValuesFromXmlNode(m_baseXmlDoc.root());
    }

    if (isSuccess)
    {
        UXAS_LOG_INFORM(s_typeName(), "::loadXml loaded ", (isBaseXml ? "base" : "extension"), " XML ", (isFile ? "file " : "string "), xml);
    }
    else
    {
        if (isBaseXml)
        {
            m_isBaseXmlDocLoaded = false;
        }
        UXAS_LOG_ERROR(s_typeName(), "::loadXml failed to load ", (isBaseXml ? "base" : "extension"), " XML ", (isFile ? "file " : "string "), xml);
    }
    return (isSuccess);
};

std::string
ConfigurationManager::getDefaultServiceXmlNode(const std::string& serviceType)
{
    std::stringstream svcXmlNode{""};
    if (m_isBaseXmlDocLoaded)
    {
        for (pugi::xml_node childNode = m_baseXmlDoc.child(StringConstant::UxAS().c_str()).first_child(); childNode; childNode = childNode.next_sibling())
        {
            UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::getDefaultServiceXmlNode childNode.name() ", childNode.name());
            UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::getDefaultServiceXmlNode childNode.attribute(StringConstant::Type().c_str()).value() ", childNode.attribute(StringConstant::Type().c_str()).value());
            if (StringConstant::Service().compare(childNode.name()) == 0
                    && (serviceType.empty()
                    || serviceType.compare(childNode.attribute(StringConstant::Type().c_str()).value()) == 0))
            {
                childNode.print(svcXmlNode);
                break;
            }
        }
        UXAS_LOG_INFORM(s_typeName(), "::getDefaultServiceXmlNode responding to ", serviceType, " XML request - returning:");
        UXAS_LOG_INFORM(svcXmlNode.str().empty() ? "\"\" (empty XML string)" : svcXmlNode.str());
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::getDefaultServiceXmlNode service XML node not available - base XML is not loaded!");
    }
    return (svcXmlNode.str());
};

pugi::xml_node
ConfigurationManager::getEnabledBridges()
{
    if (m_isBaseXmlDocLoaded && !m_isEnabledBridgesXmlDocBuilt)
    {
        // build XML document
        m_enabledBridgesXmlDoc.reset();
        pugi::xml_node uxasNode = m_enabledBridgesXmlDoc.append_child(StringConstant::UxAS().c_str());
        populateEnabledComponentXmlNode(uxasNode, StringConstant::Bridge());
        m_isEnabledBridgesXmlDocBuilt = true;
#ifdef DEBUG_LOGGING_ENABLED
        std::stringstream bridgeXmlNd{""};
        m_enabledServicesXmlDoc.print(bridgeXmlNd);
        UXAS_LOG_DEBUGGING(s_typeName(), "::getEnabledBridges built bridge XML: ", bridgeXmlNd.str());
#endif
    }
    return (m_enabledBridgesXmlDoc.child(uxas::common::StringConstant::UxAS().c_str()));
};

pugi::xml_node
ConfigurationManager::getEnabledServices()
{
    if (m_isBaseXmlDocLoaded && !m_isEnabledServicesXmlDocBuilt)
    {
        // build XML document
        m_enabledServicesXmlDoc.reset();
        pugi::xml_node uxasNode = m_enabledServicesXmlDoc.append_child(StringConstant::UxAS().c_str());
        populateEnabledComponentXmlNode(uxasNode, StringConstant::Service());
        m_isEnabledServicesXmlDocBuilt = true;
#ifdef DEBUG_LOGGING_ENABLED
        std::stringstream svcXmlNd{""};
        m_enabledServicesXmlDoc.print(svcXmlNd);
        UXAS_LOG_DEBUGGING(s_typeName(), "::getEnabledServices built service XML: ", svcXmlNd.str());
#endif
    }
    return (m_enabledServicesXmlDoc.child(uxas::common::StringConstant::UxAS().c_str()));
};


void
ConfigurationManager::populateEnabledComponentXmlNode(pugi::xml_node& uxasNode, const std::string& nodeName)
{
    pugi::xml_attribute verAtt = uxasNode.append_attribute("FormatVersion");
    verAtt.set_value("1.0");
    pugi::xml_attribute entityIdAtt = uxasNode.append_attribute(StringConstant::EntityID().c_str());
    entityIdAtt.set_value(std::to_string(getEntityId()).c_str());
    pugi::xml_attribute entityTypeAtt = uxasNode.append_attribute(StringConstant::EntityType().c_str());
    entityTypeAtt.set_value(getEntityType().c_str());

    for (pugi::xml_node baseNode = m_baseXmlDoc.child(StringConstant::UxAS().c_str()).first_child(); baseNode; baseNode = baseNode.next_sibling())
    {
        if (nodeName.compare(baseNode.name()) == 0)
        {
            // add copy of base XML component node to the enabled XML
            uxasNode.append_copy(baseNode);
//            UXAS_LOG_DEBUGGING(s_typeName(), "::populateEnabledComponentXmlNode appended new copy of base ", cmpntType->first, " XML node");
        }
    }
};

bool
ConfigurationManager::setEntityValuesFromXmlNode(const pugi::xml_node& xmlNode)
{
    bool isSuccess{true};

    pugi::xml_node entityInfoXmlNode = xmlNode.child(StringConstant::UxAS().c_str());
    if (entityInfoXmlNode)
    {
        if (!entityInfoXmlNode.attribute(StringConstant::EntityID().c_str()).empty())
        {
            s_entityId = entityInfoXmlNode.attribute(StringConstant::EntityID().c_str()).as_uint();
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode set entity ID ", s_entityId);
        }
        else
        {
            isSuccess = false;
            UXAS_LOG_ERROR(s_typeName(), "::setEntityFromXmlNode failed to set entity ID from XML");
        }

        if (isSuccess && !entityInfoXmlNode.attribute(StringConstant::EntityType().c_str()).empty())
        {
            s_entityType = entityInfoXmlNode.attribute(StringConstant::EntityType().c_str()).value();
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode set entity type ", s_entityType);
        }
        else
        {
            isSuccess = false;
            UXAS_LOG_ERROR(s_typeName(), "::setEntityFromXmlNode failed to set entity type from XML");
        }

        if (isSuccess && !entityInfoXmlNode.attribute(StringConstant::ConsoleLoggerSeverityLevel().c_str()).empty())
        {
            bool isValidLogSeverityLevel{true};
            std::string consoleLoggerSeverityLevel = entityInfoXmlNode.attribute(StringConstant::ConsoleLoggerSeverityLevel().c_str()).value();
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode processing ", StringConstant::ConsoleLoggerSeverityLevel(), " [", consoleLoggerSeverityLevel, "] from XML");
            if (uxas::common::log::LogSeverityLevelString::LOGDEBUG().compare(consoleLoggerSeverityLevel) == 0)
            {
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::ConsoleLogger::s_defaultUxasConsoleLoggerName(), uxas::common::log::LogSeverityLevel::UXASDEBUG);
            }
            else if (uxas::common::log::LogSeverityLevelString::LOGINFO().compare(consoleLoggerSeverityLevel) == 0)
            {
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::ConsoleLogger::s_defaultUxasConsoleLoggerName(), uxas::common::log::LogSeverityLevel::UXASINFO);
            }
            else if (uxas::common::log::LogSeverityLevelString::LOGWARN().compare(consoleLoggerSeverityLevel) == 0)
            {
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::ConsoleLogger::s_defaultUxasConsoleLoggerName(), uxas::common::log::LogSeverityLevel::UXASWARNING);
            }
            else if (uxas::common::log::LogSeverityLevelString::LOGERROR().compare(consoleLoggerSeverityLevel) == 0)
            {
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::ConsoleLogger::s_defaultUxasConsoleLoggerName(), uxas::common::log::LogSeverityLevel::UXASERROR);
            }
            else
            {
                isValidLogSeverityLevel = false;
            }
            if (isValidLogSeverityLevel)
            {
                UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode set ", StringConstant::ConsoleLoggerSeverityLevel(), " [", consoleLoggerSeverityLevel, "] from XML");
            }
            else
            {
                UXAS_LOG_WARN(s_typeName(), "::setEntityFromXmlNode ignoring invalid ", StringConstant::ConsoleLoggerSeverityLevel(), " [", consoleLoggerSeverityLevel, "] from XML");
            }
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode retained default ", StringConstant::ConsoleLoggerSeverityLevel());
        }

        if (isSuccess && !entityInfoXmlNode.attribute(StringConstant::MainFileLoggerSeverityLevel().c_str()).empty())
        {
            bool isValidLogSeverityLevel{true};
            std::string mainFileLoggerSeverityLevel = entityInfoXmlNode.attribute(StringConstant::MainFileLoggerSeverityLevel().c_str()).value();
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode processing ", StringConstant::MainFileLoggerSeverityLevel(), " [", mainFileLoggerSeverityLevel, "] from XML");
            if (uxas::common::log::LogSeverityLevelString::LOGDEBUG().compare(mainFileLoggerSeverityLevel) == 0)
            {
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::HeadLogDataDatabaseLogger::s_defaultUxasMainHeadLogDataDatabaseLoggerName(), uxas::common::log::LogSeverityLevel::UXASINFO); //info is lowest DB log level
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::FileLogger::s_defaultUxasMainFileLoggerName(), uxas::common::log::LogSeverityLevel::UXASDEBUG);
            }
            else if (uxas::common::log::LogSeverityLevelString::LOGINFO().compare(mainFileLoggerSeverityLevel) == 0)
            {
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::HeadLogDataDatabaseLogger::s_defaultUxasMainHeadLogDataDatabaseLoggerName(), uxas::common::log::LogSeverityLevel::UXASINFO);
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::FileLogger::s_defaultUxasMainFileLoggerName(), uxas::common::log::LogSeverityLevel::UXASINFO);
            }
            else if (uxas::common::log::LogSeverityLevelString::LOGWARN().compare(mainFileLoggerSeverityLevel) == 0)
            {
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::HeadLogDataDatabaseLogger::s_defaultUxasMainHeadLogDataDatabaseLoggerName(), uxas::common::log::LogSeverityLevel::UXASWARNING);
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::FileLogger::s_defaultUxasMainFileLoggerName(), uxas::common::log::LogSeverityLevel::UXASWARNING);
            }
            else if (uxas::common::log::LogSeverityLevelString::LOGERROR().compare(mainFileLoggerSeverityLevel) == 0)
            {
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::HeadLogDataDatabaseLogger::s_defaultUxasMainHeadLogDataDatabaseLoggerName(), uxas::common::log::LogSeverityLevel::UXASERROR);
                uxas::common::log::LogManager::getInstance().setLoggersSeverityLevelByName(uxas::common::log::FileLogger::s_defaultUxasMainFileLoggerName(), uxas::common::log::LogSeverityLevel::UXASERROR);
            }
            else
            {
                isValidLogSeverityLevel = false;
            }
            if (isValidLogSeverityLevel)
            {
                UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode set ", StringConstant::MainFileLoggerSeverityLevel(), " [", mainFileLoggerSeverityLevel, "] from XML");
            }
            else
            {
                UXAS_LOG_WARN(s_typeName(), "::setEntityFromXmlNode ignoring invalid ", StringConstant::MainFileLoggerSeverityLevel(), " [", mainFileLoggerSeverityLevel, "] from XML");
            }
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode retained default ", StringConstant::MainFileLoggerSeverityLevel());
        }

        if (isSuccess && !entityInfoXmlNode.attribute(StringConstant::StartDelay_ms().c_str()).empty())
        {
            s_startDelay_ms = entityInfoXmlNode.attribute(StringConstant::StartDelay_ms().c_str()).as_uint();
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode set start delay milliseconds ", s_startDelay_ms);
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode retained default start delay milliseconds ", s_startDelay_ms);
        }

        if (isSuccess && !entityInfoXmlNode.attribute(StringConstant::RunDuration_s().c_str()).empty())
        {
            s_runDuration_s = entityInfoXmlNode.attribute(StringConstant::RunDuration_s().c_str()).as_uint();
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode set run duration seconds ", s_runDuration_s);
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode retained default run duration seconds ", s_runDuration_s);
        }

        if (isSuccess && !entityInfoXmlNode.attribute(StringConstant::isLoggingThreadId().c_str()).empty())
        {
            s_isLoggingThreadId = entityInfoXmlNode.attribute(StringConstant::isLoggingThreadId().c_str()).as_bool();
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode setting isLoggingThreadId ", s_isLoggingThreadId);
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode retained default isLoggingThreadId ", s_isLoggingThreadId);
        }

        if (isSuccess && !entityInfoXmlNode.attribute(StringConstant::isDataTimestamp().c_str()).empty())
        {
          s_isDataTimestamp = entityInfoXmlNode.attribute(StringConstant::isDataTimestamp().c_str()).as_bool();
          UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode setting isDataTimeStamp ", s_isDataTimestamp);
        }
        else
        {
          UXAS_LOG_INFORM(s_typeName(), "::setEntityFromXmlNode retained default isDataTimeStamp ", s_isDataTimestamp);
        }
        uxas::common::log::LogManager::getInstance().m_isLoggingThreadId = s_isLoggingThreadId;
    }

    return (isSuccess);
};

void ConfigurationManager::loadUtilityValuesFromXmlNode(const pugi::xml_node& xmlNode)
{
    pugi::xml_node xmlUxasNode = xmlNode.child(StringConstant::UxAS().c_str());
    if (xmlUxasNode)
    {
        for (auto currentXmlNode = xmlUxasNode.first_child(); currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
        {
#if defined(USE_GEO_LIBS)
            if ((std::string(currentXmlNode.name()) == std::string("Utility"))
                    && (!currentXmlNode.attribute("Type").empty()) &&
                    (currentXmlNode.attribute("Type").value() == std::string("DtedLookup")))
            {
                std::string pathToFiles;
                if (!currentXmlNode.attribute("PathToFiles").empty())
                {
                    pathToFiles = std::string(currentXmlNode.attribute("PathToFiles").value());
                    // make sure it ends with a '/'
                    pathToFiles = (*(pathToFiles.rbegin()) == '/') ? (pathToFiles) : (pathToFiles + "/"); 
                }
                for (auto dtedFileXmlNode = currentXmlNode.first_child(); dtedFileXmlNode; dtedFileXmlNode = dtedFileXmlNode.next_sibling())
                {
                    if ((std::string(dtedFileXmlNode.name()) == std::string("DtedFile"))
                            && (!dtedFileXmlNode.attribute("FileName").empty()))
                    {
                        std::string fileName = dtedFileXmlNode.attribute("FileName").value();
                        if(!fileName.empty())
                        {
                            std::string pathFile = pathToFiles + fileName;
                            utilities::GroundHeight::getInstance().isLoadDtedFile(pathFile);
                        }
                    }
                }
            }
#endif
        }
    }
}





// <editor-fold defaultstate="collapsed" desc="buildUxasMasterFile cfg file UTILITY ONLY">

/*
//bool
//ConfigurationManager::buildUxasMasterFile()
//{
//
//    //richard@ICET3:~/data/dev/n_refactor/uxas$ ls code/uxas/test/xml
//    ///home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml
//
//    std::vector<std::string> xmlFilePaths;
//
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_cmpnt.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_PathPlanner_Euclidean_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_SendTestMessages_01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_SendTestMessages_02.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestAxisVideo_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestConfig.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestConfig2.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestExternalBridge_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestFilterRadarHits_Test00.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestGarminGPS_Test00.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestGarminGPS_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestGarminGPS_Test02.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestGenerateAirVehicleStates_Test00.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestHoustonRadar_Test00.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestHoustonRadar_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestHoustonRadar_Test02.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestHoustonRadar_Test03.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestHoustonRadar_Test04.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestICET_CCA_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestICET_CCA_Test02.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestImpactTasks_Test01_ImpactPointSearch.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestImpactTasks_Test02_ImpactLineSearch.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestImpactTasks_Test03_PatternSearch.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestImpactTasks_Test04_AngledAreaSearch.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestImpactTasks_Test05_SurfaceVehicles.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestImpactTasks_Test06_GroundVehicles.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestImpactTasks_test07_AirSurfaceGroundVehicle.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestImpactTasks_test08_WatchTask.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestMessageLogging.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestPiccolo_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestPubPullAndSubPushBridges_Test01a.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestPubPullAndSubPushBridges_Test01b.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestRangeTest_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestSendMessages_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestSerialBridge_Test01a.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestSerialBridge_Test01b.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestTcpBridge_Test01a.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestTcpBridge_Test01b.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestTcpBridge_Test02a.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestTcpBridge_Test02b.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestTrackConnections_a.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestTrackConnections_b.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestVicsInterface_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestVicsInterface_Test02.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestVicsInterface_Test03.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestVicsInterface_Test04.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestVicsLogger_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestZyre_Test01a.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestZyre_Test01b.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestZyre_Test02a.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestZyre_Test02b.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestZyreBridge_Test01a.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_TestZyreBridge_Test01b.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_UxAS_Kestrel_01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_WaypointPlanManager_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_ZZ_ComponentCreationAndDeletion_Test01.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_ZZ_ComponentCreationAndDeletion_Test02a.xml");
//    xmlFilePaths.emplace_back("/home/richard/data/dev/n_refactor/uxas/code/uxas/test/xml/cfg_ZZ_ComponentCreationAndDeletion_Test02b.xml");
//
//    std::set<std::string> cmpntTypes;
//    std::stringstream cmpntTypesStrStrm;
//    std::unordered_map<std::string, uint32_t> cmpntCntByType;
//    std::unordered_map<std::string, std::string> cmpntXmlByType;
//    std::unordered_map<std::string, std::unordered_map<std::string, uint32_t>> uniqueSingleCmpntXmlByType;
//    for (auto& path : xmlFilePaths)
//    {
//        std::ifstream xmlInputStream(path);
//        pugi::xml_document xmlDoc;
//        pugi::xml_parse_result xmlParseSuccess = xmlDoc.load(xmlInputStream);
//
//        if (xmlParseSuccess)
//        {
////            std::string xmlDocRootNm = xmlDoc.root().name();
////            UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile xmlDoc.root().name() ", xmlDoc.root().name());
//            pugi::xml_node uxasNode = xmlDoc.child(StringConstant::UxAS().c_str());
//            UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile uxasNode.name() ", uxasNode.name(), " FILE ", path); // GOOD
////            pugi::xml_node t_cmpntsNode = uxasNode.child(StringConstant::Components().c_str());
////            UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile t_cmpntsNode.name() ", t_cmpntsNode.name(), " FILE ", path); // GOOD
////            pugi::xml_node t_firstCmpntNode = t_cmpntsNode.first_child();
////            UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile t_firstCmpntNode.name() ", t_firstCmpntNode.name(), " FILE ", path); // GOOD
//            
//            pugi::xml_node cmpntNodes = xmlDoc.child(StringConstant::UxAS().c_str()).child(StringConstant::Components().c_str());            
//
//            for (pugi::xml_node uxasChildNode = uxasNode.first_child(); uxasChildNode; uxasChildNode = uxasChildNode.next_sibling())
//            {
//                UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile uxasChildNode.name() ", uxasChildNode.name(), " FILE ", path);
////                if (StringConstant::Components().compare(uxasChildNode.name()) == 0)
////                {
//
//
////                for (pugi::xml_node ndCurrent = ndConfigurationEntries.first_child(); ndCurrent; ndCurrent = ndCurrent.next_sibling())
//                
//
//                for (pugi::xml_node cmpntsChildNode = uxasChildNode.first_child(); cmpntsChildNode; cmpntsChildNode = cmpntsChildNode.next_sibling())
//                {
//                    if (StringConstant::Component().compare(cmpntsChildNode.name()) == 0)
//                    {
//                        auto cmpntType = cmpntCntByType.find(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value());
//                        if (cmpntType == cmpntCntByType.end())
//                        {
//                            cmpntCntByType.emplace(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value(), 1);
//                            std::stringstream svcXmlNode{""};
//                            cmpntsChildNode.print(svcXmlNode);
//                            svcXmlNode; // << std::endl;
//                            cmpntXmlByType.emplace(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value(), svcXmlNode.str());
//                            //uniqueSingleCmpntXmlByType
//                            cmpntTypes.emplace(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value());
//                            cmpntTypesStrStrm << cmpntsChildNode.attribute(StringConstant::Type().c_str()).value() << ",";
//                            UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile found type ", cmpntsChildNode.attribute(StringConstant::Type().c_str()).value());
//                            auto unqCmpntTypeXml = uniqueSingleCmpntXmlByType.find(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value());
//                            if (unqCmpntTypeXml == uniqueSingleCmpntXmlByType.end())
//                            {
//                                uniqueSingleCmpntXmlByType.emplace(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value(), std::unordered_map<std::string, uint32_t>());
//                            }
//                            auto unqCmpntXml = uniqueSingleCmpntXmlByType.at(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value()).find(svcXmlNode.str());
//                            if (unqCmpntXml == uniqueSingleCmpntXmlByType.at(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value()).end())
//                            {
//                                uniqueSingleCmpntXmlByType.at(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value()).emplace(svcXmlNode.str(), 1);
//                            }
//                        }
//                        else
//                        {
//                            cmpntType->second++;
//                            auto cmpntXml = cmpntXmlByType.find(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value());
//                            std::stringstream svcXmlNode{""};
//                            cmpntsChildNode.print(svcXmlNode);
//                            svcXmlNode; // << std::endl;
//                            if (cmpntXml == cmpntXmlByType.end()) // not expected
//                            {
//                                cmpntXmlByType.emplace(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value(), svcXmlNode.str());
//                                UXAS_LOG_WARN(s_typeName(), "::buildUxasMasterFile unexpectedly found type ", cmpntsChildNode.attribute(StringConstant::Type().c_str()).value());
//                            }
//                            else
//                            {
//                                cmpntXml->second = (cmpntXml->second + svcXmlNode.str());
//                                UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile appending XML for type ", cmpntsChildNode.attribute(StringConstant::Type().c_str()).value());
//                            }
//                            auto unqCmpntTypeXml = uniqueSingleCmpntXmlByType.find(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value());
//                            if (unqCmpntTypeXml == uniqueSingleCmpntXmlByType.end())
//                            {
//                                uniqueSingleCmpntXmlByType.emplace(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value(), std::unordered_map<std::string, uint32_t>());
//                            }
//                            auto unqCmpntXml = uniqueSingleCmpntXmlByType.at(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value()).find(svcXmlNode.str());
//                            if (unqCmpntXml == uniqueSingleCmpntXmlByType.at(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value()).end())
//                            {
//                                uniqueSingleCmpntXmlByType.at(cmpntsChildNode.attribute(StringConstant::Type().c_str()).value()).emplace(svcXmlNode.str(), 1);
//                            }
//                        }
//                        std::stringstream svcXmlNodeRaw{""};
//                        cmpntsChildNode.print(svcXmlNodeRaw);
//                        svcXmlNodeRaw; // << std::endl;
//                        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile XML ", svcXmlNodeRaw.str());
//                    }
//                }
//                //                }
//            }
//        }
//        else
//        {
//            UXAS_LOG_WARN(s_typeName(), "::buildUxasMasterFile failed to parse XML from ", path);
//        }
//    }
// 
//    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML SUMMARY START ");
//    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML SUMMARY START ");
//    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML SUMMARY START ");
//    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component types ", cmpntTypesStrStrm.str());
//
//    UXAS_LOG_INFORM("");
//    
//    for (auto itCmpntCnt = cmpntCntByType.cbegin(), itEndCmpntCnt = cmpntCntByType.cend(); itCmpntCnt != itEndCmpntCnt; itCmpntCnt++)
//    {
//        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component type ", itCmpntCnt->first, " occurrence count is ", itCmpntCnt->second);
//    }
//    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML SUMMARY END ");
//    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML SUMMARY END ");
//    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML SUMMARY END ");
//    
//    UXAS_LOG_INFORM("");
//    
////    std::unordered_map<std::string, uint32_t> uniqueCmpntXmlCnt;
////    for (auto itCmpntXml = cmpntXmlByType.cbegin(), itEndCmpntXml = cmpntXmlByType.cend(); itCmpntXml != itEndCmpntXml; itCmpntXml++)
////    {
//////        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML START START START for type ", itCmpntXml->first);
//////        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML START START START for type ", itCmpntXml->first);
//////        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML START START START for type ", itCmpntXml->first);
////        auto uniqueCmpntXmlIt = uniqueCmpntXmlCnt.find(itCmpntXml->second);
////        if (uniqueCmpntXmlIt == uniqueCmpntXmlCnt.end())
////        {
////            uniqueCmpntXmlCnt.emplace(itCmpntXml->second, 1);
////            UXAS_LOG_INFORM(itCmpntXml->second);
////        }
////        else
////        {
////            uniqueCmpntXmlIt->second++;
////        }
//////        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML END END END ");
//////        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML END END END ");
//////        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML END END END ");
////    }
////
////    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML CONCLUSION START ");
////    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML CONCLUSION START ");
////    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML CONCLUSION START ");
////    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component types ", cmpntTypesStrStrm.str());
////
////    UXAS_LOG_INFORM("");
////    
////    for (auto itUniqueXmlCnt = uniqueCmpntXmlCnt.cbegin(), itUniqueXmlCntEnd = cmpntCntByType.cend(); itUniqueXmlCnt != itUniqueXmlCntEnd; itUniqueXmlCnt++)
////    {
////        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML unique occurrence count is ", itUniqueXmlCnt->second);
////    }
////    UXAS_LOG_INFORM("");
////    
////    for (auto itUniqueXmlCnt = uniqueCmpntXmlCnt.cbegin(), itUniqueXmlCntEnd = cmpntCntByType.cend(); itUniqueXmlCnt != itUniqueXmlCntEnd; itUniqueXmlCnt++)
////    {
////        UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML unique occurrence count is ", itUniqueXmlCnt->second, " for XML ", itUniqueXmlCnt->first);
////    }
////    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML CONCLUSION END ");
////    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML CONCLUSION END ");
////    UXAS_LOG_INFORM(s_typeName(), "::buildUxasMasterFile component XML CONCLUSION END ");
////    
////    UXAS_LOG_INFORM("");
//
//    for (auto _cTypeIt = uniqueSingleCmpntXmlByType.cbegin(), _cTypeItEnd = uniqueSingleCmpntXmlByType.cend(); _cTypeIt != _cTypeItEnd; _cTypeIt++)
//    {
//        for (auto _cTypeXmlIt = _cTypeIt->second.cbegin(), _cTypeXmlItEnd = _cTypeIt->second.cend(); _cTypeXmlIt != _cTypeXmlItEnd; _cTypeXmlIt++)
//        {
//            UXAS_LOG_INFORM(_cTypeXmlIt->first);
//        }
//    }
//
//
//    
//    return (true);
//};
 */

// </editor-fold>

}; //namespace common
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ServiceManager.h"
#include "LmcpObjectNetworkBridgeManager.h"

#define INCLUDE_SERVICE_HEADERS //this switches 00_ServiceList.h to load the service headers
#include "00_ServiceList.h"

#include "uxas/messages/uxnative/CreateNewService.h"
#include "uxas/messages/uxnative/KillService.h"
#include "uxas/messages/uxnative/StartupComplete.h"

#include "UxAS_ConfigurationManager.h"
#include "Constants/UxAS_String.h"
#include "UxAS_Log.h"

#include "stdUniquePtr.h"

#include "Constants/Constant_Strings.h"

#include "FileSystemUtilities.h"

#if (defined(__APPLE__) && defined(__MACH__))
#define OSX
#endif

#if (!defined(_WIN32) && !defined( __CYGWIN__))
#include <unistd.h>
#ifndef OSX
#include <linux/reboot.h>
#endif
#include <sys/reboot.h>
#endif

#include <fstream>
#include <stdexcept>

namespace uxas
{
namespace service
{

std::unique_ptr<ServiceManager> ServiceManager::s_instance = nullptr;

ServiceManager&
ServiceManager::getInstance()
{
    // first time/one time creation
    if (ServiceManager::s_instance == nullptr)
    {
        UXAS_LOG_INFORM(s_typeName(), "::getInstance static ServiceBase subclass initialization started");
        // force initialization of classes and their static class members

        //// <editor-fold defaultstate="collapsed" desc="trigger static Service class initialization"> 
        // REGISTER SERVICES
        #define REGISTER_SERVICE_CODE
        #include "00_ServiceList.h"        
        //// </editor-fold>
        
        UXAS_LOG_INFORM(s_typeName(), "::getInstance static Service class initialization succeeded");

        s_instance.reset(new ServiceManager);
    }

    return *s_instance;
};

bool
ServiceManager::configureServiceManager()
{
    UXAS_LOG_DEBUGGING(s_typeName(), "::configureServiceManager - START");

    m_isBaseClassKillServiceProcessingPermitted = true;
    // increase service manager termination time-outs
    m_subclassTerminationAbortDuration_ms = 600000;
    m_subclassTerminationWarnDuration_ms = 180000;

    bool isSuccess = configureService((uxas::common::ConfigurationManager::getInstance().getRootDataWorkDirectory()),
            uxas::common::ConfigurationManager::getInstance().getEnabledServices()
            .find_child_by_attribute(uxas::common::StringConstant::Service().c_str()
            , uxas::common::StringConstant::Type().c_str(), s_typeName().c_str()));

    if (isSuccess)
    {
        addSubscriptionAddress(uxas::messages::uxnative::CreateNewService::Subscription);
        m_isConfigured = true;
        UXAS_LOG_INFORM(s_typeName(), "::configureServiceManager succeeded configuration");
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::configureServiceManager failed configuration");
    }

    UXAS_LOG_DEBUGGING(s_typeName(), "::configureServiceManager - END");
    return (isSuccess);
};

void
ServiceManager::run()
{
    runUntil(UINT32_MAX);
};

void
ServiceManager::runUntil(uint32_t duration_s)
{
    UXAS_LOG_DEBUGGING(s_typeName(), "::runUntil - START");
    auto startTime = std::chrono::system_clock::now();
    while (std::chrono::duration_cast<std::chrono::seconds>(
            std::chrono::system_clock::now() - startTime).count() < duration_s)
    {
        {
            std::lock_guard<std::mutex> lock(m_servicesByIdMutex);
            uint32_t runningSvcCnt = removeTerminatedServices();
            if (m_isServiceManagerTermination && runningSvcCnt < 1)
            {
                UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(),"****** ServiceManager has been Requested To Terminate !!! ******");
                break;
            }
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(500));
    }
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(),"****** ServiceManager has started Terminating Services !!! ******");
    if (!m_isServiceManagerTermination) // run duration exit
    {
        terminateAllServices();
        uint32_t checkTerminateAttemptCount{0};
        uint32_t runningSvcCnt{UINT32_MAX};
        while (checkTerminateAttemptCount++ < 20)
        {
            {
                std::lock_guard<std::mutex> lock(m_servicesByIdMutex);
                runningSvcCnt = removeTerminatedServices();
                if (runningSvcCnt < 1)
                {
                    break;
                }
            }
            std::this_thread::sleep_for(std::chrono::milliseconds(500));
        }
        if (runningSvcCnt < 1)
        {
            UXAS_LOG_INFORM(s_typeName(), "::runUntil all services terminated after [", checkTerminateAttemptCount, "] check termination attempts (run duration exit)");
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::runUntil [", runningSvcCnt, "] services remain after [", checkTerminateAttemptCount, "] check termination attempts (run duration exit)");
        }
    }
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(),"****** All Services have been Terminated !!! ******");

    // terminate my client thread
    m_isTerminateNetworkClient = true;
    uint32_t checkBaseTerminateCount{0};
    while (!m_isBaseClassTerminationFinished && checkBaseTerminateCount++ < 20)
    {
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(),"****** ServiceManager is Terminating it's Client Thread !!! ******");
        std::this_thread::sleep_for(std::chrono::milliseconds(500));
    }
    if (m_isServiceManagerTermination) // service manager termination exit
    {
        if (m_isBaseClassTerminationFinished)
        {
            UXAS_LOG_INFORM(s_typeName(), "::runUntil found base class terminated after [", checkBaseTerminateCount, "] attempts (service manager termination exit)");
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::runUntil aborted effort to terminate base class after [", checkBaseTerminateCount, "] attempts (service manager termination exit)");
        }
        UXAS_LOG_INFORM(s_typeName(), "::runUntil invoking shutdownProcessor method (service manager termination exit)");
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(),"****** ServiceManager is Running the Processor Shutdown Routine !!! ******");
        shutdownProcessor();
    }
    else
    {
        if (m_isBaseClassTerminationFinished)
        {
            UXAS_LOG_INFORM(s_typeName(), "::runUntil found base class terminated after [", checkBaseTerminateCount, "] attempts (run duration exit)");
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::runUntil aborted effort to terminate base class after [", checkBaseTerminateCount, "] attempts (run duration exit)");
        }
    }

    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(),"****** ServiceManager is Finished Shutting Down !!! ******");
    UXAS_LOG_DEBUGGING(s_typeName(), "::runUntil - END");
};

bool
ServiceManager::initialize()
{
    UXAS_LOG_DEBUGGING(s_typeName(), "::initialize - START");
    bool isSuccess{false};
    if (m_isConfigured)
    {
        uint32_t serviceCreationSuccessCount{0};
        uint32_t serviceCreationFailureCount{0};

        pugi::xml_node uxasEnabledSvcsXml = uxas::common::ConfigurationManager::getInstance().getEnabledServices();
        if (!uxasEnabledSvcsXml.empty())
        {
            isSuccess = true;
            for (pugi::xml_node svcNode = uxasEnabledSvcsXml.first_child(); svcNode; svcNode = svcNode.next_sibling())
            {
                if (s_typeName().compare(svcNode.attribute(uxas::common::StringConstant::Type().c_str()).value()) == 0)
                {
                    UXAS_LOG_INFORM(s_typeName(), "::initialize ignoring ", s_typeName(), " XML configuration node");
                    continue;
                }

                int32_t finalServiceId{-1};
                if (createService(svcNode,finalServiceId))
                {
                    serviceCreationSuccessCount++;
                }
                else
                {
                    isSuccess = false;
                    serviceCreationFailureCount++;
                }
            }
        }

        if (isSuccess)
        {
            if (serviceCreationSuccessCount > 0)
            {
                UXAS_LOG_INFORM(s_typeName(), "::initialize successfully initialized and started all ", serviceCreationSuccessCount, " services");
            }
            else
            {
                UXAS_LOG_WARN(s_typeName(), "::initialize unexpectedly initialized and started zero services");
            }
            std::unique_ptr<uxas::messages::uxnative::StartupComplete> startupComplete = uxas::stduxas::make_unique<uxas::messages::uxnative::StartupComplete>();
            sendLmcpObjectBroadcastMessage(std::move(startupComplete));
        }
        else if (uxasEnabledSvcsXml.empty())
        {
            UXAS_LOG_ERROR(s_typeName(), "::initialize failed to get non-empty XML configuration node");
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::initialize failed to initialize and start ", serviceCreationFailureCount, " services; successfully started ", serviceCreationSuccessCount, " services");
        }
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::initialize failed - must invoke configure method BEFORE calling initialize");
    }

    UXAS_LOG_DEBUGGING(s_typeName(), "::initialize - END");
    return (isSuccess);
};

uint32_t
ServiceManager::removeTerminatedServices() // lock m_servicesByIdMutex before invoking
{   
    uint32_t runningSvcCnt{0};
    uint32_t terminatedSvcCnt{0};
    for (auto svcIt = m_servicesById.begin(); svcIt != m_servicesById.end();)
    {
        if (svcIt->second->getIsTerminationFinished())
        {
            UXAS_LOG_INFORM(s_typeName(), "::removeTerminatedServices removing reference to terminated ", svcIt->second->m_networkClientTypeName, " ID ", svcIt->second->m_networkId);
            terminatedSvcCnt++;
            svcIt = m_servicesById.erase(svcIt); // remove finished service (enables destruction)
        }
        else
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::removeTerminatedServices retaining reference to non-terminated ", svcIt->second->m_networkClientTypeName, " ID ", svcIt->second->m_networkId);
            runningSvcCnt++;
            svcIt++;
        }
    }
    
    // check to see if bridges are ready for termination
    uxas::communications::LmcpObjectNetworkBridgeManager::getInstance().removeTerminatedBridges(runningSvcCnt, terminatedSvcCnt);
    
    UXAS_LOG_INFORM(s_typeName(), "::removeTerminatedServices retained [", runningSvcCnt, "] services and removed [", terminatedSvcCnt, "] services");
    return (runningSvcCnt);
};

bool
ServiceManager::createService(const std::string& serviceXml, int64_t newServiceId)
{
    // TODO REVIEW 
    // Q1: if serviceXml only contains the service type, then merge 
    // default config XML from local file?
    // 
    // Q2: is valid case to create a service without any XML config values
    // (using hard-coded values exclusively)?
    bool isSuccess{false};

    pugi::xml_document xmlDoc;
    pugi::xml_parse_result xmlParseSuccess = xmlDoc.load(serviceXml.c_str());
    if (xmlParseSuccess)
    {
        if (uxas::common::StringConstant::UxAS().compare(xmlDoc.root().name()) == 0)
        {
            isSuccess = createService(xmlDoc.first_child(),newServiceId);
        }
        else
        {
            if (!std::string(xmlDoc.root().name()).empty())
            {
                isSuccess = createService(xmlDoc.root(),newServiceId);
            }
            else
            {
                isSuccess = createService(xmlDoc.first_child(),newServiceId);
            }
        }
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::createService failed to parse XML string [", serviceXml, "]");
    }

    return (isSuccess);
};

bool
ServiceManager::createService(const pugi::xml_node& serviceXmlNode, int64_t newServiceId)
{
    // 20150904 RJT - currently accepting either:
    // (a) "Component" node (legacy code requesting service via CreateNewService message) 
    // (b) "Service" node (new service code)
    if (uxas::common::StringConstant::Service().compare(serviceXmlNode.name()) == 0)
    {
        UXAS_LOG_INFORM(s_typeName(), "::createService received ", serviceXmlNode.name(), " XML node");
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::createService received ", serviceXmlNode.name(), " XML node - expecting ", uxas::common::StringConstant::Service(), " XML node");
    }

    std::unique_ptr<ServiceBase> newService = instantiateConfigureInitializeStartService(serviceXmlNode, 0, newServiceId);
    if (newService)
    {
        UXAS_LOG_INFORM(s_typeName(), "::createService successfully created ", newService->m_networkClientTypeName, " service ID ", newService->m_networkId);
        m_servicesById.emplace(newService->m_networkId, std::move(newService));
        return (true);
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::createService failed to create a service");
        return (false);
    }
};

std::unordered_map<uint32_t, std::unique_ptr<ServiceBase>>
ServiceManager::createTestServices(const std::string& cfgXmlFilePath, uint32_t entityId, int64_t firstNetworkId)
{
    std::unordered_map<uint32_t, std::unique_ptr<ServiceBase>> testServicesByNetworkIdMap;
    UXAS_LOG_INFORM(s_typeName(), "::createTestServices - START");
//#ifdef GOOGLE_TEST_BRIDGES_ENABLED

    int64_t networkId = firstNetworkId;
    std::ifstream cfgXmlInputStream(cfgXmlFilePath);
    pugi::xml_document xmlDoc;
    pugi::xml_parse_result xmlParseSuccess = xmlDoc.load(cfgXmlInputStream);

    if (xmlParseSuccess)
    {
        for (pugi::xml_node serviceOrBridgeXmlNode = xmlDoc.child(uxas::common::StringConstant::UxAS().c_str()).first_child();
                serviceOrBridgeXmlNode; serviceOrBridgeXmlNode = serviceOrBridgeXmlNode.next_sibling())
        {
            if (uxas::common::StringConstant::Service().compare(serviceOrBridgeXmlNode.name()) == 0)
            {
                std::unique_ptr<ServiceBase> newTestService = instantiateConfigureInitializeStartService(serviceOrBridgeXmlNode, entityId, networkId);
                networkId++;
                if (newTestService)
                {
                    UXAS_LOG_INFORM(s_typeName(), "::createTestServices added ", newTestService->m_networkClientTypeName, " service with entity ID ", newTestService->m_entityId," and service ID ", newTestService->m_networkId, " from XML configuration ", cfgXmlFilePath);
                    testServicesByNetworkIdMap.emplace(newTestService->m_networkId, std::move(newTestService));
                }
                else
                {
                    UXAS_LOG_ERROR(s_typeName(), "::createTestServices failed to add a service from XML configuration ", cfgXmlFilePath);
                }
            }
        }
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::createTestServices failed to load configuration XML from location ", cfgXmlFilePath);
    }
    UXAS_LOG_INFORM(s_typeName(), "::createTestServices - END");

//#endif // GOOGLE_TEST_BRIDGES_ENABLED
    return (testServicesByNetworkIdMap);
};

std::unique_ptr<ServiceBase>
ServiceManager::instantiateConfigureInitializeStartService(const pugi::xml_node& serviceXmlNode, uint32_t entityId, int64_t networkId)
{
    UXAS_LOG_INFORM(s_typeName(), "::instantiateConfigureInitializeStartService - START");
    std::unique_ptr<ServiceBase> newServiceFinal;
    
    std::string serviceType;
    if ((uxas::common::StringConstant::Component().compare(serviceXmlNode.name()) == 0 // Component node
            || uxas::common::StringConstant::Service().compare(serviceXmlNode.name()) == 0) // Service node
            && !serviceXmlNode.attribute(uxas::common::StringConstant::Type().c_str()).empty() // not empty Type attribute
            && (s_typeName().compare(serviceXmlNode.attribute(uxas::common::StringConstant::Type().c_str()).value()) != 0)) // type is not ServiceManager
    {
        serviceType = serviceXmlNode.attribute(uxas::common::StringConstant::Type().c_str()).value();
        UXAS_LOG_INFORM(s_typeName(), "::createService processing ", serviceXmlNode.name(), " XML node for type ", serviceType);
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::createService not processing ", serviceXmlNode.name(), " XML node since node name is empty, invalid or disallowed", uxas::common::StringConstant::Type());
        return (newServiceFinal);
    }
    
    std::unique_ptr<ServiceBase> newService = ServiceBase::instantiateService(serviceType);

    if (newService)
    {
        UXAS_LOG_INFORM(s_typeName(), "::instantiateConfigureInitializeStartService successfully instantiated ", newService->m_serviceType, " service ID ", newService->m_networkId, " and work directory name [", newService->m_workDirectoryName, "]");
        if (newService->configureService(uxas::common::ConfigurationManager::getInstance().getRootDataWorkDirectory(), serviceXmlNode))
        {
            //TODO - consider friend of clientBase (protect m_entityId and m_entityIdString)
            // support test bridges
            int64_t networkIdLocal{newService->m_networkId};
            uint32_t entityIdLocal{newService->m_entityId};
            bool isPassedInID{false};
            if(networkId > 0)
            {
                networkIdLocal = networkId;
                isPassedInID = true;
            }
            if(entityId > 0)
            {
                entityIdLocal = entityId;
                isPassedInID = true;
            }
            
            if (isPassedInID)
            {
                std::string originalUnicastAddress = LmcpObjectNetworkClientBase::getNetworkClientUnicastAddress(newService->m_entityId, newService->m_networkId);
                newService->m_entityId = entityIdLocal;
                newService->m_entityIdString = std::to_string(entityIdLocal);
                newService->m_networkId = networkIdLocal;
                newService->m_networkIdString = std::to_string(networkIdLocal);
                newService->m_serviceId = networkIdLocal;
                newService->removeSubscriptionAddress(originalUnicastAddress);
                newService->addSubscriptionAddress(LmcpObjectNetworkClientBase::getNetworkClientUnicastAddress(newService->m_entityId, newService->m_networkId));
                UXAS_LOG_INFORM(s_typeName(), "::instantiateConfigureInitializeStartService re-configuring ", newService->m_networkClientTypeName, " entity ID ", newService->m_entityId, " service ID ", newService->m_networkId);
            }
            UXAS_LOG_INFORM(s_typeName(), "::instantiateConfigureInitializeStartService successfully configured ", newService->m_networkClientTypeName, " entity ID ", newService->m_entityId, " service ID ", newService->m_networkId);
            if (newService->initializeAndStartService())
            {
                newServiceFinal = std::move(newService);
                UXAS_LOG_INFORM(s_typeName(), "::instantiateConfigureInitializeStartService successfully initialized and started ", newServiceFinal->m_networkClientTypeName, " service ID ", newServiceFinal->m_networkId);
            }
            else
            {
                UXAS_LOG_ERROR(s_typeName(), "::instantiateConfigureInitializeStartService failed to initialize and start ", newService->m_networkClientTypeName, " service ID ", newService->m_networkId);
            }
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::instantiateConfigureInitializeStartService failed to configure ", newService->m_networkClientTypeName, " service ID ", newService->m_networkId);
        }
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::instantiateConfigureInitializeStartService failed to instantiate ", serviceType);
    }
    
    UXAS_LOG_INFORM(s_typeName(), "::instantiateConfigureInitializeStartService - END");
    return (newServiceFinal);
};

bool
ServiceManager::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    bool isTerminateOnReturn{false};
    if (uxas::messages::uxnative::isCreateNewService(receivedLmcpMessage->m_object.get()))
    {
        auto createNewService = std::static_pointer_cast<uxas::messages::uxnative::CreateNewService>(receivedLmcpMessage->m_object);
        std::string xmlConfig = createNewService->getXmlConfiguration() + "\n";
        uxas::common::StringUtil::ReplaceAll(xmlConfig, "&lt;", "<");
        uxas::common::StringUtil::ReplaceAll(xmlConfig, "&gt;", ">");
        for (auto& msg : createNewService->getEntityConfigurations())
        {
            xmlConfig += msg->toXML() + "\n";
        }
        for (auto& msg : createNewService->getEntityStates())
        {
            xmlConfig += msg->toXML() + "\n";
        }
        for (auto& msg : createNewService->getMissionCommands())
        {
            xmlConfig += msg->toXML() + "\n";
        }
        for (auto& msg : createNewService->getAreas())
        {
            xmlConfig += msg->toXML() + "\n";
        }
        for (auto& msg : createNewService->getLines())
        {
            xmlConfig += msg->toXML() + "\n";
        }
        for (auto& msg : createNewService->getPoints())
        {
            xmlConfig += msg->toXML() + "\n";
        }
        for (auto& msg : createNewService->getKeepInZones())
        {
            xmlConfig += msg->toXML() + "\n";
        }
        for (auto& msg : createNewService->getKeepOutZones())
        {
            xmlConfig += msg->toXML() + "\n";
        }
        for (auto& msg : createNewService->getOperatingRegions())
        {
            xmlConfig += msg->toXML() + "\n";
        }
        xmlConfig += "</Service>";
        if (createService(xmlConfig,createNewService->getServiceID()))
        {
            UXAS_LOG_INFORM(s_typeName(), "::processReceivedLmcpMessage created service using XML configuration from message payload");
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::processReceivedLmcpMessage failed to create service request via messaging");
        }
    }
    else if (uxas::messages::uxnative::isKillService(receivedLmcpMessage->m_object.get()))
    {
        auto killService = std::static_pointer_cast<uxas::messages::uxnative::KillService>(receivedLmcpMessage->m_object);
//        std::cout << std::endl << "******ServiceManager::processReceivedLmcpMessage::m_networkId[" 
//                << m_networkId << "]  killService->getServiceID[" << killService->getServiceID() << "] !! ******" << std::endl << std::endl;
        if (killService->getServiceID() == m_networkId)
        {
            terminateAllServices();
        }
        else if(killService->getServiceID() == -1)
        {
            std::cout << std::endl << "******ServiceManager::processReceivedLmcpMessage::terminateAllServices() !! ******" << std::endl << std::endl;
            m_isServiceManagerTermination = true;
            terminateAllServices();
            isTerminateOnReturn = true;
        }
    }

    return (isTerminateOnReturn); // always false implies never terminating service from here
};

void
ServiceManager::terminateAllServices()
{
    // Kill all bridges first
    uxas::communications::LmcpObjectNetworkBridgeManager::getInstance().terminateAllBridges();
    
    // send KillService message to any non-terminated services
    std::lock_guard<std::mutex> lock(m_servicesByIdMutex);
    for (auto svcIt = m_servicesById.cbegin(), serviceItEnd = m_servicesById.cend(); svcIt != serviceItEnd; svcIt++)
    {
        if (svcIt->second && !svcIt->second->getIsTerminationFinished())
        {
            UXAS_LOG_INFORM(s_typeName(), "::terminateAllServices sending [", uxas::messages::uxnative::KillService::TypeName, "] message to ", svcIt->second->m_serviceType, " having entity ID [", svcIt->second->m_entityId, "] and service ID [", svcIt->second->m_serviceId, "]");

            std::cout << std::endl << s_typeName() << "::terminateAllServices sending [" << uxas::messages::uxnative::KillService::TypeName << "] message to " << svcIt->second->m_serviceType << " having entity ID [" << svcIt->second->m_entityId << "] and service ID [" << svcIt->second->m_serviceId << "]" << std::endl;
            auto killService = uxas::stduxas::make_unique<uxas::messages::uxnative::KillService>();
            killService->setServiceID(svcIt->second->m_networkId);
            sendLmcpObjectLimitedCastMessage(getNetworkClientUnicastAddress(m_entityIdString, svcIt->second->m_networkId), std::move(killService));
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::terminateAllServices unexpectedly found empty pointer (hosting a service object)");
        }
    }
};

void
ServiceManager::shutdownProcessor()
{
    UXAS_LOG_INFORM(s_typeName(), "::shutdownProcessor - START");
#ifdef ICET_ARM // only shutdown ARM processors
    UXAS_LOG_INFORM(s_typeName(), "::shutdownProcessor synchronization and reboot - START");
    sync();
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
#ifndef OSX
    reboot(LINUX_REBOOT_CMD_POWER_OFF);
#else
    reboot(RB_AUTOBOOT);
#endif
    UXAS_LOG_INFORM(s_typeName(), "::shutdownProcessor synchronization and reboot - END");
#endif
    UXAS_LOG_INFORM(s_typeName(), "::shutdownProcessor - END");
};


}; //namespace service
}; //namespace uxas

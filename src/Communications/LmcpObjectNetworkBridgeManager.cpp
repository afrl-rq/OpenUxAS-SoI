// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LmcpObjectNetworkBridgeManager.h"
#include "ServiceManager.h"

#include "LmcpObjectNetworkSerialBridge.h"
#include "LmcpObjectNetworkTcpBridge.h"
#include "LmcpObjectNetworkSubscribePushBridge.h"
#include "LmcpObjectNetworkPublishPullBridge.h"
#include "LmcpObjectNetworkZeroMqZyreBridge.h"

#include "UxAS_ConfigurationManager.h"
#include "Constants/UxAS_String.h"
#include "UxAS_Log.h"
#include "uxas/messages/uxnative/KillService.h"

#include "stdUniquePtr.h"

#include "LmcpObjectNetworkSerialBridge.h"
#include "ImpactSubscribePushBridge.h"

#include <fstream>
#include <stdexcept>

namespace uxas
{
namespace communications
{

std::unique_ptr<LmcpObjectNetworkBridgeManager> LmcpObjectNetworkBridgeManager::s_instance = nullptr;

LmcpObjectNetworkBridgeManager&
LmcpObjectNetworkBridgeManager::getInstance()
{
    // first time/one time creation
    if (LmcpObjectNetworkBridgeManager::s_instance == nullptr)
    {
        s_instance.reset(new LmcpObjectNetworkBridgeManager);
    }

    return *s_instance;
};

void
LmcpObjectNetworkBridgeManager::terminateAllBridges()
{
    for (auto svcIt = m_bridgesByNetworkId.cbegin(), serviceItEnd = m_bridgesByNetworkId.cend(); svcIt != serviceItEnd; svcIt++)
    {
        if (svcIt->second && !svcIt->second->getIsTerminationFinished())
        {
            UXAS_LOG_INFORM(s_typeName(), "::terminateAllBridges sending [", uxas::messages::uxnative::KillService::TypeName, "] message to ", svcIt->second->m_networkClientTypeName, " having entity ID [", svcIt->second->m_entityId, "] and network ID [", svcIt->second->m_networkId, "]");

            std::cout << std::endl << s_typeName() << "::terminateAllBridges sending [" << uxas::messages::uxnative::KillService::TypeName << "] message to " << svcIt->second->m_networkClientTypeName << " having entity ID [" << svcIt->second->m_entityId << "] and network ID [" << svcIt->second->m_networkId << "]" << std::endl;
            auto killService = uxas::stduxas::make_unique<uxas::messages::uxnative::KillService>();
            killService->setServiceID(svcIt->second->m_networkId);
            uxas::service::ServiceManager::getInstance().sendLmcpObjectLimitedCastMessage(LmcpObjectNetworkClientBase::getNetworkClientUnicastAddress(svcIt->second->m_entityId, svcIt->second->m_networkId), std::move(killService));
        }
        else
        {
            UXAS_LOG_INFORM(s_typeName(), "::terminateAllBridges unexpectedly found empty pointer (hosting a bridge object)");
        }
    }
}

void
LmcpObjectNetworkBridgeManager::removeTerminatedBridges(uint32_t &runningSvcCnt, uint32_t &terminatedSvcCnt)
{
    for (auto svcIt = m_bridgesByNetworkId.begin(); svcIt != m_bridgesByNetworkId.end();)
    {
        if (svcIt->second->getIsTerminationFinished())
        {
            UXAS_LOG_INFORM(s_typeName(), "::removeTerminatedServices removing reference to terminated ", svcIt->second->m_networkClientTypeName, " ID ", svcIt->second->m_networkId);
            terminatedSvcCnt++;
            svcIt = m_bridgesByNetworkId.erase(svcIt); // remove finished service (enables destruction)
        }
        else
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::removeTerminatedServices retaining reference to non-terminated ", svcIt->second->m_networkClientTypeName, " ID ", svcIt->second->m_networkId);
            runningSvcCnt++;
            svcIt++;
        }
    }
}

bool
LmcpObjectNetworkBridgeManager::initialize()
{
    bool isSuccess{false};
    if (!m_isInitializedBridges)
    {
        uint32_t addedBridgeXmlNodeCount = 0;
        uint32_t failedBridgeXmlNodeCount = 0;
        pugi::xml_node uxasEnabledBridgesXml = uxas::common::ConfigurationManager::getInstance().getEnabledBridges();
        if (!uxasEnabledBridgesXml.empty())
        {
            for (pugi::xml_node bridgeNode = uxasEnabledBridgesXml.first_child(); bridgeNode; bridgeNode = bridgeNode.next_sibling())
            {
                std::unique_ptr<LmcpObjectNetworkClientBase> newBridge = createBridge(bridgeNode, UINT32_MAX, UINT32_MAX);
                if (newBridge)
                {
                    addedBridgeXmlNodeCount++;
                    m_bridgesByNetworkId.emplace(newBridge->m_networkId, std::move(newBridge));
                    UXAS_LOG_INFORM(s_typeName(), "::initialize number of added bridges is ", addedBridgeXmlNodeCount);
                }
                else
                {
                    failedBridgeXmlNodeCount++;
                    UXAS_LOG_WARN(s_typeName(), "::initialize number of failed bridge add attempts is ", failedBridgeXmlNodeCount);
                }
            }
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::initialize did not find any enabled bridges");
        }
        m_isInitializedBridges = true;
        isSuccess = true;
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::initialize ignoring second attempt to instantiate bridges from XML");
    }

    return (isSuccess);
};

std::unordered_map<uint32_t, std::unique_ptr<LmcpObjectNetworkClientBase>>
LmcpObjectNetworkBridgeManager::createTestBridges(const std::string& cfgXmlFilePath, uint32_t entityId, uint32_t firstNetworkId)
{
    std::unordered_map<uint32_t, std::unique_ptr<LmcpObjectNetworkClientBase>> testBridgesByNetworkIdMap;
    UXAS_LOG_INFORM(s_typeName(), "::createTestBridges - START");
//#ifdef GOOGLE_TEST_BRIDGES_ENABLED
    uint32_t networkId = firstNetworkId;
    std::ifstream cfgXmlInputStream(cfgXmlFilePath);
    pugi::xml_document xmlDoc;
    pugi::xml_parse_result xmlParseSuccess = xmlDoc.load(cfgXmlInputStream);

    if (xmlParseSuccess)
    {
        for (pugi::xml_node serviceOrBridgeXmlNode = xmlDoc.child(uxas::common::StringConstant::UxAS().c_str()).first_child();
                serviceOrBridgeXmlNode; serviceOrBridgeXmlNode = serviceOrBridgeXmlNode.next_sibling())
        {
            if (uxas::common::StringConstant::Bridge().compare(serviceOrBridgeXmlNode.name()) == 0)
            {
                std::unique_ptr<LmcpObjectNetworkClientBase> newTestBridge = createBridge(serviceOrBridgeXmlNode, entityId, networkId);
                networkId++;
                if (newTestBridge)
                {
                    UXAS_LOG_INFORM(s_typeName(), "::createTestBridges added ", newTestBridge->m_networkClientTypeName, " bridge with entity ID ", newTestBridge->m_entityId," and network ID ", newTestBridge->m_networkId, " from XML configuration ", cfgXmlFilePath);
                    testBridgesByNetworkIdMap.emplace(newTestBridge->m_networkId, std::move(newTestBridge));
                }
                else
                {
                    UXAS_LOG_ERROR(s_typeName(), "::createTestBridges failed to add a bridge from XML configuration ", cfgXmlFilePath);
                }
            }
        }
    }
    else
    {
        UXAS_LOG_ERROR(s_typeName(), "::createTestBridges failed to load configuration XML from location ", cfgXmlFilePath);
    }
    UXAS_LOG_INFORM(s_typeName(), "::createTestBridges - END");

//#endif // GOOGLE_TEST_BRIDGES_ENABLED
    return (testBridgesByNetworkIdMap);
};

std::unique_ptr<LmcpObjectNetworkClientBase>
LmcpObjectNetworkBridgeManager::createBridge(const pugi::xml_node& bridgeXmlNode, uint32_t entityId, uint32_t networkId)
{
    // attempt instantiation of new bridge
    std::unique_ptr<LmcpObjectNetworkClientBase> newBridgeFinal;
    if (uxas::common::StringConstant::Bridge().compare(bridgeXmlNode.name()) == 0)
    {
        std::string bridgeType = bridgeXmlNode.attribute(uxas::common::StringConstant::Type().c_str()).value();
        UXAS_LOG_INFORM(s_typeName(), "::createBridge adding ", bridgeType);
        
        std::unique_ptr<LmcpObjectNetworkClientBase> newBridge;
        if (LmcpObjectNetworkSerialBridge::s_typeName().compare(bridgeType) == 0)
        {
            newBridge = uxas::stduxas::make_unique<LmcpObjectNetworkSerialBridge>();
        }
        else if (LmcpObjectNetworkTcpBridge::s_typeName().compare(bridgeType) == 0)
        {
            newBridge = uxas::stduxas::make_unique<LmcpObjectNetworkTcpBridge>();
        }
        else if (LmcpObjectNetworkSubscribePushBridge::s_typeName().compare(bridgeType) == 0)
        {
            newBridge = uxas::stduxas::make_unique<LmcpObjectNetworkSubscribePushBridge>();
        }
        else if (LmcpObjectNetworkPublishPullBridge::s_typeName().compare(bridgeType) == 0)
        {
            newBridge = uxas::stduxas::make_unique<LmcpObjectNetworkPublishPullBridge>();
        }
        else if (LmcpObjectNetworkZeroMqZyreBridge::s_typeName().compare(bridgeType) == 0)
        {
            newBridge = uxas::stduxas::make_unique<LmcpObjectNetworkZeroMqZyreBridge>();
        }
        else if (ImpactSubscribePushBridge::s_typeName().compare(bridgeType) == 0)
        {
            newBridge = uxas::stduxas::make_unique<ImpactSubscribePushBridge>();
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::createBridge cannot construct ", bridgeType);
        }

        if (newBridge)
        {
            UXAS_LOG_INFORM(s_typeName(), "::createBridge instantiated bridge ", bridgeType, " network ID ", newBridge->m_networkId);
            if (newBridge->configureNetworkClient(bridgeType, LmcpObjectNetworkClientBase::ReceiveProcessingType::SERIALIZED_LMCP, bridgeXmlNode))
            {
                //TODO - consider friend of clientBase (protect m_entityId and m_entityIdString)
                // support test bridges
                if (entityId < UINT32_MAX && networkId < UINT32_MAX)
                {
                    std::string originalUnicastAddress = LmcpObjectNetworkClientBase::getNetworkClientUnicastAddress(newBridge->m_entityId, newBridge->m_networkId);
                    newBridge->m_entityId = entityId;
                    newBridge->m_entityIdString = std::to_string(newBridge->m_entityId);
                    newBridge->m_networkId = networkId;
                    newBridge->removeSubscriptionAddress(originalUnicastAddress);
                    newBridge->addSubscriptionAddress(LmcpObjectNetworkClientBase::getNetworkClientUnicastAddress(newBridge->m_entityId, newBridge->m_networkId));
                    UXAS_LOG_WARN(s_typeName(), "::createBridge re-configuring ", newBridge->m_networkClientTypeName, " entity ID ", newBridge->m_entityId, " network ID ", newBridge->m_networkId);
                }
                UXAS_LOG_INFORM(s_typeName(), "::createBridge configured ", newBridge->m_networkClientTypeName, " entity ID ", newBridge->m_entityId, " network ID ", newBridge->m_networkId);
                if (newBridge->initializeAndStart())
                {
                    newBridgeFinal = std::move(newBridge);
                    UXAS_LOG_INFORM(s_typeName(), "::createBridge initialized and started ", newBridgeFinal->m_networkClientTypeName, " network ID ", newBridgeFinal->m_networkId);
                }
                else
                {
                    UXAS_LOG_ERROR(s_typeName(), "::createBridge failed to initialize and start ", newBridge->m_networkClientTypeName, " network ID ", newBridge->m_networkId);
                    newBridge.reset();
                }
            }
            else
            {
                UXAS_LOG_ERROR(s_typeName(), "::createBridge failed to configure ", newBridge->m_networkClientTypeName, " network ID ", newBridge->m_networkId);
            }
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::createBridge failed to instantiate ", bridgeType);
        }
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::createBridge ignoring ", bridgeXmlNode.name(), " XML node - expecting ", uxas::common::StringConstant::Bridge(), " XML node");
    }

    return (newBridgeFinal);
};

}; //namespace communications
}; //namespace uxas

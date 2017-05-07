// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_TaskTracker.cpp
 * Author: derek
 * 
 * Created on Aug 2, 2015, 8:21 AM
 */

#include "OperatingRegionStateService.h"

#include "UxAS_Log.h"
#include "pugixml.hpp"

#include <map>
#include <algorithm>

#define STRING_COMPONENT_NAME "OpRegionState"
#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME
#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"

namespace uxas
{
namespace service
{
OperatingRegionStateService::ServiceBase::CreationRegistrar<OperatingRegionStateService>
OperatingRegionStateService::s_registrar(OperatingRegionStateService::s_registryServiceTypeNames());

OperatingRegionStateService::OperatingRegionStateService()
: ServiceBase(OperatingRegionStateService::s_typeName(), OperatingRegionStateService::s_directoryName())
{
};

OperatingRegionStateService::~OperatingRegionStateService()
{
};

bool
OperatingRegionStateService::configure(const pugi::xml_node& serviceXmlNode)
{
    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::RemoveZones::Subscription);

    m_region.reset(new afrl::cmasi::OperatingRegion);
    m_region->setID(0); // YEAR2: simply match all requests from agent

    return true;
}

bool
OperatingRegionStateService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    if (afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
    {
        auto kzone = std::static_pointer_cast<afrl::cmasi::KeepInZone>(receivedLmcpMessage->m_object);
        bool addZone = true;
        for (auto z : m_region->getKeepInAreas())
        {
            if (z == kzone->getZoneID())
            {
                addZone = false;
                break;
            }
        }
        if (addZone)
        {
            m_region->getKeepInAreas().push_back(kzone->getZoneID());
            auto sendMsg = std::static_pointer_cast<avtas::lmcp::Object>(m_region);
            sendSharedLmcpObjectBroadcastMessage(sendMsg);
        }
    }
    else if (afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
    {
        auto kzone = std::static_pointer_cast<afrl::cmasi::KeepOutZone>(receivedLmcpMessage->m_object);
        bool addZone = true;
        for (auto z : m_region->getKeepOutAreas())
        {
            if (z == kzone->getZoneID())
            {
                addZone = false;
                break;
            }
        }
        if (addZone)
        {
            m_region->getKeepOutAreas().push_back(kzone->getZoneID());
            auto sendMsg = std::static_pointer_cast<avtas::lmcp::Object>(m_region);
            sendSharedLmcpObjectBroadcastMessage(sendMsg);
        }
    }
    else if (afrl::cmasi::isRemoveZones(receivedLmcpMessage->m_object.get()))
    {
        auto rzones = std::static_pointer_cast<afrl::cmasi::RemoveZones>(receivedLmcpMessage->m_object);
        for (auto z : rzones->getZoneList())
        {
            // keep in zone removal
            std::vector<int64_t>& ki = m_region->getKeepInAreas();
            std::vector<int64_t>::iterator ki_end = std::remove_if(ki.begin(), ki.end(),
                    [&](int64_t val) {
                        return (val == z); });
            ki.erase(ki_end, ki.end());

            // keep out zone removal
            std::vector<int64_t>& ko = m_region->getKeepOutAreas();
            std::vector<int64_t>::iterator ko_end = std::remove_if(ko.begin(), ko.end(),
                    [&](int64_t val) {
                        return (val == z); });
            ko.erase(ko_end, ko.end());
        }

        auto sendMsg = std::static_pointer_cast<avtas::lmcp::Object>(m_region);
        sendSharedLmcpObjectBroadcastMessage(sendMsg);
    }
    return (false); // always false implies never terminating service from here
}

}; //namespace service
}; //namespace uxas

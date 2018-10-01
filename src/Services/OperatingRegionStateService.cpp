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

#define STRING_XML_ADDITIONAL_PADDING "AdditionalPadding"

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
    m_additionalPadding = serviceXmlNode.attribute(STRING_XML_ADDITIONAL_PADDING).as_double(0.0);

    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::RemoveZones::Subscription);
    addSubscriptionAddress(afrl::impact::WaterZone::Subscription);


    m_region.reset(new afrl::cmasi::OperatingRegion);
    m_region->setID(0); // YEAR2: simply match all requests from agent

    return true;
}

bool
OperatingRegionStateService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    bool addZone = false;
    bool removeZone = false;
    if (afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
    {
        auto kzone = std::static_pointer_cast<afrl::cmasi::KeepInZone>(receivedLmcpMessage->m_object);

        addZone = true;
        for (auto z : m_region->getKeepInAreas())
        {
            if (z == kzone->getZoneID())
            {
                addZone = false;
                break;
            }
        }
        removeZone = kzone->getStartTime() == -1 && kzone->getEndTime() == -1;
        if (addZone && !removeZone)
        {
            if(m_additionalPadding > 1e-4)
            {
                kzone->setPadding( kzone->getPadding() + m_additionalPadding );
                sendSharedLmcpObjectBroadcastMessage(kzone);
            }
            m_region->getKeepInAreas().push_back(kzone->getZoneID());
            IMPACT_INFORM("Added Keep In Zone ", kzone->getZoneID(), " ", kzone->getLabel());
        }
        if (removeZone)
        {
            std::vector<int64_t>& ki = m_region->getKeepInAreas();
            std::vector<int64_t>::iterator ki_end = std::remove_if(ki.begin(), ki.end(),
                [&](int64_t val) {
                return (val == kzone->getZoneID()); });
            ki.erase(ki_end, ki.end());
            IMPACT_INFORM("Removed Keep In Zone ", kzone->getZoneID(), " ", kzone->getLabel());

        }
    }
    else if (afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
    {
        auto kzone = std::static_pointer_cast<afrl::cmasi::KeepOutZone>(receivedLmcpMessage->m_object);

        addZone = true;
        for (auto z : m_region->getKeepOutAreas())
        {
            if (z == kzone->getZoneID())
            {
                addZone = false;
                break;
            }
        }
        removeZone = kzone->getStartTime() == -1 && kzone->getEndTime() == -1;

        if (addZone && !removeZone)
        {
            if(m_additionalPadding > 1e-4)
            {
                kzone->setPadding( kzone->getPadding() + m_additionalPadding );
                sendSharedLmcpObjectBroadcastMessage(kzone);
            }
            m_region->getKeepOutAreas().push_back(kzone->getZoneID());
            IMPACT_INFORM("Added Keep Out Zone ", kzone->getZoneID(), " ", kzone->getLabel());
        }

        if (removeZone)
        {
            std::vector<int64_t>& ko = m_region->getKeepOutAreas();
            std::vector<int64_t>::iterator ko_end = std::remove_if(ko.begin(), ko.end(),
                [&](int64_t val) {
                return (val == kzone->getZoneID()); });
            ko.erase(ko_end, ko.end());
            IMPACT_INFORM("Removed Keep In Zone ", kzone->getZoneID(), " ", kzone->getLabel());
        }
    }
    else if (afrl::impact::isWaterZone(receivedLmcpMessage->m_object.get()))
    {
        auto wzone = std::static_pointer_cast<afrl::impact::WaterZone>(receivedLmcpMessage->m_object);
        IMPACT_INFORM("Recieved Water Zone ", wzone->getZoneID(), " ", wzone->getLabel());
    }
    else if (afrl::cmasi::isRemoveZones(receivedLmcpMessage->m_object.get()))
    {
        auto rzones = std::static_pointer_cast<afrl::cmasi::RemoveZones>(receivedLmcpMessage->m_object);
        removeZone = true; //assume
        for (auto z : rzones->getZoneList())
        {
            // keep in zone removal
            std::vector<int64_t>& ki = m_region->getKeepInAreas();
            std::vector<int64_t>::iterator ki_end = std::remove_if(ki.begin(), ki.end(),
                [&](int64_t val) {
                return (val == z); });
            ki.erase(ki_end, ki.end());
            IMPACT_INFORM("Removed Keep In Zone ", z);

            // keep out zone removal
            std::vector<int64_t>& ko = m_region->getKeepOutAreas();
            std::vector<int64_t>::iterator ko_end = std::remove_if(ko.begin(), ko.end(),
                [&](int64_t val) {
                return (val == z); });
            ko.erase(ko_end, ko.end());
            IMPACT_INFORM("Removed Keep Out Zone ", z);

        }
    }

    if (addZone || removeZone) {
        auto sendMsg = std::static_pointer_cast<avtas::lmcp::Object>(m_region);
        sendSharedLmcpObjectBroadcastMessage(sendMsg);
        IMPACT_INFORM("Working Operating Region KIZs ", m_region->getKeepInAreas().size(), " KOZs ", m_region->getKeepOutAreas().size());
    }

    return (false); // always false implies never terminating service from here
}
}; //namespace service
}; //namespace uxas

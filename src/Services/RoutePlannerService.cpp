// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_RoutePlanner.cpp
 * Author: derek
 * 
 * Created on Aug 2, 2015, 8:21 AM
 */

#include "RoutePlannerService.h"

#include "UxAS_Log.h"
#include "UnitConversions.h"
#include "Constants/Convert.h"
#include "Constants/UxAS_String.h"

#include "afrl/cmasi/CMASI.h"
#include "afrl/impact/IMPACT.h"
#include "uxas/messages/route/ROUTE.h"

#include "pugixml.hpp"

#include <algorithm>

#define STRING_COMPONENT_NAME "RoutePlanner"
#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"

namespace uxas
{
namespace service
{
RoutePlannerService::ServiceBase::CreationRegistrar<RoutePlannerService>
RoutePlannerService::s_registrar(RoutePlannerService::s_registryServiceTypeNames());

RoutePlannerService::RoutePlannerService()
: ServiceBase(RoutePlannerService::s_typeName(), RoutePlannerService::s_directoryName())
{
};

RoutePlannerService::~RoutePlannerService()
{
};

bool
RoutePlannerService::configure(const pugi::xml_node& serviceXmlNode)
{
    // Need to track:
    //  (1) environment construction (keep-in/keep-out zones and operating region)
    //  (2) current states of entities for non-specified start locations
    //  (3) entity configurations to determine kinematic and/or dynamic constraints
    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    addSubscriptionAddress(afrl::impact::WaterZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::OperatingRegion::Subscription);
    
    //ENTITY CONFIGURATIONS
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
    for(auto child : childconfigs)
        addSubscriptionAddress(child);
    
    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);
    
    // service 'global' path planning requests (system assumes aircraft)
    addSubscriptionAddress(uxas::messages::route::RoutePlanRequest::Subscription);
    
    // requests directed to an aircraft planner should also be handled
    addSubscriptionAddress(uxas::common::MessageGroup::AircraftPathPlanner());

    return true;
}

bool
RoutePlannerService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    if (uxas::messages::route::isRoutePlanRequest(receivedLmcpMessage->m_object.get()))
    {
        std::shared_ptr<uxas::messages::route::RoutePlanRequest> request = std::static_pointer_cast<uxas::messages::route::RoutePlanRequest>(receivedLmcpMessage->m_object);
        // only handle requests for air and surface vehicles
        if (m_airVehicles.find(request->getVehicleID()) != m_airVehicles.end() ||
                m_surfaceVehicles.find(request->getVehicleID()) != m_surfaceVehicles.end())
        {
            std::shared_ptr<uxas::messages::route::RoutePlanResponse> response = HandleRoutePlanRequestMsg(request);
            std::shared_ptr<avtas::lmcp::Object> pResponse = std::static_pointer_cast<avtas::lmcp::Object>(response);
            // always limited-cast route plan responses
            sendSharedLmcpObjectLimitedCastMessage(
                    getNetworkClientUnicastAddress(
                        receivedLmcpMessage->m_attributes->getSourceEntityId(),
                        receivedLmcpMessage->m_attributes->getSourceServiceId()
                    ),
                    pResponse);
        }
    }
    else if (afrl::cmasi::isEntityState(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
        m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        // no region update for generic entities
    }
    else if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpMessage->m_object))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
        m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);

        // check for unknown vehicle
        if (m_airVehicles.find(id) == m_airVehicles.end())
        {
            UpdateRegions(receivedLmcpMessage->m_object);
        }
        m_airVehicles.insert(id);
    }
    else if (afrl::vehicles::isGroundVehicleState(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
        m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        m_groundVehicles.insert(id);
        // no region update for ground vehicles
    }
    else if (afrl::vehicles::isSurfaceVehicleState(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
        m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);

        // check for unknown vehicle
        if (m_surfaceVehicles.find(id) == m_surfaceVehicles.end())
        {
            UpdateRegions(receivedLmcpMessage->m_object);
        }
        m_surfaceVehicles.insert(id);
    }
    else if (afrl::cmasi::isEntityConfiguration(receivedLmcpMessage->m_object))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
        m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        // no region update for generic entities
    }
    else if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(receivedLmcpMessage->m_object))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
        m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);

        // check for unknown vehicle
        if (m_airVehicles.find(id) == m_airVehicles.end())
        {
            UpdateRegions(receivedLmcpMessage->m_object);
        }
        m_airVehicles.insert(id);
    }
    else if (afrl::vehicles::isGroundVehicleConfiguration(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
        m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        m_groundVehicles.insert(id);
        // no region updates for ground vehicles
    }
    else if (afrl::vehicles::isSurfaceVehicleConfiguration(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();

        // check for unknown vehicle
        if (m_entityConfigurations.find(id) == m_entityConfigurations.end())
        {
            UpdateRegions(receivedLmcpMessage->m_object); // force update for new surface vehicles with embedded keep-in water zone
        }
        m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        m_surfaceVehicles.insert(id);
    }
    else if (afrl::impact::isWaterZone(receivedLmcpMessage->m_object.get()))
    {
        auto wzone = std::static_pointer_cast<afrl::impact::WaterZone>(receivedLmcpMessage->m_object);
        m_waterZones[wzone->getZoneID()] = wzone;

        // check all surface vehicle configurations with this zone referenced
        for (auto e : m_entityConfigurations)
        {
            if (afrl::vehicles::isSurfaceVehicleConfiguration(e.second.get()))
            {
                auto s = std::dynamic_pointer_cast<afrl::vehicles::SurfaceVehicleConfiguration>(e.second);
                if (s->getWaterArea() == wzone->getZoneID())
                {
                    UpdateRegions(std::dynamic_pointer_cast<avtas::lmcp::Object>(s));
                }
            }
        }
    }
    else if (afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
    {
        std::shared_ptr<afrl::cmasi::KeepInZone> kiZone = std::static_pointer_cast<afrl::cmasi::KeepInZone>(receivedLmcpMessage->m_object);
        int64_t id = kiZone->getZoneID();
        auto zone = m_keepInZones.find(id);
        if (zone != m_keepInZones.end())
        {
            if (!(zone->second->operator==(*kiZone)))
            {
                UpdateRegions(receivedLmcpMessage->m_object); // an existing region was updated
            }
        }
        m_keepInZones[id] = kiZone;
    }
    else if (afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
    {
        std::shared_ptr<afrl::cmasi::KeepOutZone> koZone = std::static_pointer_cast<afrl::cmasi::KeepOutZone>(receivedLmcpMessage->m_object);
        int64_t id = koZone->getZoneID();
        auto zone = m_keepOutZones.find(id);
        if (zone != m_keepOutZones.end())
        {
            if (!(zone->second->operator==(*koZone)))
            {
                UpdateRegions(receivedLmcpMessage->m_object);
            }
        }
        m_keepOutZones[id] = koZone;
    }
    else if (afrl::cmasi::isOperatingRegion(receivedLmcpMessage->m_object.get()))
    {
        std::shared_ptr<afrl::cmasi::OperatingRegion> region = std::static_pointer_cast<afrl::cmasi::OperatingRegion>(receivedLmcpMessage->m_object);
        int64_t id = region->getID();
        auto r = m_operatingRegions.find(id);
        if (r != m_operatingRegions.end())
        {
            if (!(r->second->operator==(*region)))
            {
                BuildVisibilityRegion(region);
            }
        }
        else
        {
            m_operatingRegions[id] = region;
            BuildVisibilityRegion(region);
        }
    }
    return (false); // always false implies never terminating service from here
}


void RoutePlannerService::BuildVisibilityRegion(std::shared_ptr<afrl::cmasi::OperatingRegion> region)
{
    // completely new/updated region, so clear everything out for all vehicles
    auto env = m_environments.find(region->getID());
    if (env != m_environments.end())
    {
        env->second.clear();
    }

    auto graph = m_visgraphs.find(region->getID());
    if (graph != m_visgraphs.end())
    {
        graph->second.clear();
    }

    // for each eligible vehicle (surface/air) build a visibility environment and graph
    for (auto id = m_airVehicles.begin(); id != m_airVehicles.end(); id++)
    {
        BuildVehicleSpecificRegion(region, *id, nullptr);
    }
    for (auto id = m_surfaceVehicles.begin(); id != m_surfaceVehicles.end(); id++)
    {
        afrl::cmasi::AbstractGeometry* waterzone = nullptr;
        auto surfaceConfig = m_entityConfigurations.find(*id);
        if (surfaceConfig != m_entityConfigurations.end())
        {
            std::shared_ptr<afrl::vehicles::SurfaceVehicleConfiguration> config = std::static_pointer_cast<afrl::vehicles::SurfaceVehicleConfiguration>(surfaceConfig->second);
            if (m_waterZones.find(config->getWaterArea()) != m_waterZones.end())
            {
                waterzone = m_waterZones[config->getWaterArea()]->getBoundary();
            }
        }
        BuildVehicleSpecificRegion(region, *id, waterzone);
    }
}

void RoutePlannerService::UpdateRegions(std::shared_ptr<avtas::lmcp::Object> msg)
{
    if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleState>(msg))
    {
        std::shared_ptr<afrl::cmasi::AirVehicleState> avstate = std::static_pointer_cast<afrl::cmasi::AirVehicleState>(msg);
        for (auto r = m_operatingRegions.begin(); r != m_operatingRegions.end(); r++)
        {
            std::shared_ptr<afrl::cmasi::OperatingRegion> region = r->second;
            BuildVehicleSpecificRegion(region, avstate->getID(), nullptr);
        }
    }
    else if (afrl::cmasi::isAirVehicleConfiguration(msg.get()))
    {
        std::shared_ptr<afrl::cmasi::AirVehicleConfiguration> avconfig = std::static_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(msg);
        for (auto r = m_operatingRegions.begin(); r != m_operatingRegions.end(); r++)
        {
            std::shared_ptr<afrl::cmasi::OperatingRegion> region = r->second;
            BuildVehicleSpecificRegion(region, avconfig->getID(), nullptr);
        }
    }
    else if (afrl::vehicles::isSurfaceVehicleState(msg.get()))
    {
        std::shared_ptr<afrl::vehicles::SurfaceVehicleState> surfstate = std::static_pointer_cast<afrl::vehicles::SurfaceVehicleState>(msg);
        for (auto r = m_operatingRegions.begin(); r != m_operatingRegions.end(); r++)
        {
            std::shared_ptr<afrl::cmasi::OperatingRegion> region = r->second;
            // don't yet have a water region, so plan without for now
            BuildVehicleSpecificRegion(region, surfstate->getID(), nullptr);
        }
    }
    else if (afrl::vehicles::isSurfaceVehicleConfiguration(msg.get()))
    {
        std::shared_ptr<afrl::vehicles::SurfaceVehicleConfiguration> surfconfig = std::static_pointer_cast<afrl::vehicles::SurfaceVehicleConfiguration>(msg);
        afrl::cmasi::AbstractGeometry* waterzone = nullptr;
        if (m_waterZones.find(surfconfig->getWaterArea()) != m_waterZones.end())
        {
            waterzone = m_waterZones[surfconfig->getWaterArea()]->getBoundary();
        }
        bool hasZeroRegion = false;
        for (auto r = m_operatingRegions.begin(); r != m_operatingRegions.end(); r++)
        {
            if (r->second->getID() == 0)
            {
                hasZeroRegion = true;
            }
            std::shared_ptr<afrl::cmasi::OperatingRegion> region = r->second;
            BuildVehicleSpecificRegion(region, surfconfig->getID(), waterzone);
        }
#ifndef _DEBUG
        if (!hasZeroRegion)
        {
            // insert zero region id for unspecified regions
            std::shared_ptr<afrl::cmasi::OperatingRegion> oregion(new afrl::cmasi::OperatingRegion);
            oregion->setID(0);
            BuildVehicleSpecificRegion(oregion, surfconfig->getID(), waterzone);
        }
#endif
    }
    else if (afrl::cmasi::isKeepInZone(msg.get()))
    {
        std::shared_ptr<afrl::cmasi::KeepInZone> zone = std::static_pointer_cast<afrl::cmasi::KeepInZone>(msg);
        int64_t zoneId = zone->getZoneID();

        // rebuild any region that contains this zone
        for (auto r = m_operatingRegions.begin(); r != m_operatingRegions.end(); r++)
        {
            std::shared_ptr<afrl::cmasi::OperatingRegion> region = r->second;
            if (std::find(region->getKeepInAreas().begin(), region->getKeepInAreas().end(), zoneId) != region->getKeepInAreas().end())
            {
                BuildVisibilityRegion(region);
            }
        }
    }
    else if (afrl::cmasi::isKeepOutZone(msg.get()))
    {
        std::shared_ptr<afrl::cmasi::KeepOutZone> zone = std::static_pointer_cast<afrl::cmasi::KeepOutZone>(msg);
        int64_t zoneId = zone->getZoneID();

        // rebuild any region that contains this zone
        for (auto r = m_operatingRegions.begin(); r != m_operatingRegions.end(); r++)
        {
            std::shared_ptr<afrl::cmasi::OperatingRegion> region = r->second;
            if (std::find(region->getKeepOutAreas().begin(), region->getKeepOutAreas().end(), zoneId) != region->getKeepOutAreas().end())
            {
                BuildVisibilityRegion(region);
            }
        }
    }
}

void RoutePlannerService::BuildVehicleSpecificRegion(std::shared_ptr<afrl::cmasi::OperatingRegion> region, int64_t vehicleId, afrl::cmasi::AbstractGeometry* geom)
{
    double epsilon = 1e-4; // millimeter accuracy + tolerance

    std::vector< VisiLibity::Polygon > polygonPlanningList;
    std::vector< VisiLibity::Polygon > polygonsToExpand;
    std::vector< double > expandValues;
    std::vector< VisiLibity::Polygon > polygonsToShrink;
    std::vector< double > shrinkValues;

    // for each polygon:
    //      linearize
    //      eliminate redundant vertices
    //      check orientation and reverse if needed
    //      enforce standard form
    //      insert to list
    VisiLibity::Bounding_Box zoneBox = { };
    bool boxInitialized = false;
    bool validKeepInZone = false;

    // add keep out zones to expansion list
    for (size_t n = 0; n < region->getKeepOutAreas().size(); n++)
    {
        auto zone = m_keepOutZones.find(region->getKeepOutAreas().at(n));
        if (zone != m_keepOutZones.end())
        {
            bool isZoneApplicable = false;
            for (size_t k = 0; k < zone->second->getAffectedAircraft().size(); k++)
            {
                if (zone->second->getAffectedAircraft().at(k) == vehicleId)
                {
                    isZoneApplicable = true;
                    break;
                }
            }

            if (isZoneApplicable || zone->second->getAffectedAircraft().empty())
            {
                VisiLibity::Polygon poly;
                afrl::cmasi::AbstractGeometry* boundary = zone->second->getBoundary();
                double delta = (zone->second->getPadding() < 0.0) ? 0.0 : zone->second->getPadding();

                // linearize
                if (LinearizeBoundary(boundary, poly))
                {
                    // remove excess points
                    poly.eliminate_redundant_vertices(1.0);

                    // ensure that the polygon is simple
                    if (poly.is_simple(epsilon))
                    {
                        // ensure that the polygon is properly oriented
                        if (poly.area() < 0)
                            poly.reverse();

                        // add to list
                        polygonsToExpand.push_back(poly);
                        expandValues.push_back(delta);

                        // update bounding box
                        if (region->getKeepInAreas().empty())
                        {
                            VisiLibity::Bounding_Box bbox;
                            bbox.x_max = poly[0].x();
                            bbox.x_min = poly[0].x();
                            bbox.y_max = poly[0].y();
                            bbox.y_min = poly[0].y();
                            for (size_t k = 1; k < poly.n(); k++)
                            {
                                double x = poly[k].x();
                                double y = poly[k].y();
                                if (x > bbox.x_max) bbox.x_max = x;
                                if (x < bbox.x_min) bbox.x_min = x;
                                if (y > bbox.y_max) bbox.y_max = y;
                                if (y < bbox.y_min) bbox.y_min = y;
                            }
                            if (!boxInitialized)
                            {
                                zoneBox.x_max = bbox.x_max;
                                zoneBox.x_min = bbox.x_min;
                                zoneBox.y_max = bbox.y_max;
                                zoneBox.y_min = bbox.y_min;
                                boxInitialized = true;
                            }
                            else
                            {
                                if (bbox.x_max > zoneBox.x_max) zoneBox.x_max = bbox.x_max;
                                if (bbox.x_min < zoneBox.x_min) zoneBox.x_min = bbox.x_min;
                                if (bbox.y_max > zoneBox.y_max) zoneBox.y_max = bbox.y_max;
                                if (bbox.y_min < zoneBox.y_min) zoneBox.y_min = bbox.y_min;
                            }
                        }
                    }
                }
            }
        }
    } // done with keep in zones

    // expand all polygons
    std::vector< VisiLibity::Polygon > expandedPolygons;
    if (VisiLibity::Polygon::offset_polygons(polygonsToExpand, expandedPolygons, expandValues, epsilon))
    {
        // add expanded polygons to complete list
        for (size_t n = 0; n < expandedPolygons.size(); n++)
        {
            // eliminate redundant vertices
            expandedPolygons[n].eliminate_redundant_vertices(1.0);

            // check orientation and reverse if necessary
            if (expandedPolygons[n].area() > 0)
                expandedPolygons[n].reverse();

            // enforce standard form
            expandedPolygons[n].enforce_standard_form();

            polygonPlanningList.push_back(expandedPolygons[n]);
        }

        // keep out zones are expanded and added, now process all keep in zones
        for (size_t n = 0; n < region->getKeepInAreas().size(); n++)
        {
            VisiLibity::Polygon poly;
            auto zone = m_keepInZones.find(region->getKeepInAreas().at(n));
            if (zone != m_keepInZones.end())
            {
                bool isZoneApplicable = false;
                for (size_t k = 0; k < zone->second->getAffectedAircraft().size(); k++)
                {
                    if (zone->second->getAffectedAircraft().at(k) == vehicleId)
                    {
                        isZoneApplicable = true;
                        break;
                    }
                }

                if (isZoneApplicable || zone->second->getAffectedAircraft().empty())
                {
                    afrl::cmasi::AbstractGeometry* boundary = zone->second->getBoundary();
                    double delta = (zone->second->getPadding() > 0.0) ? 0.0 : zone->second->getPadding();

                    // linearize
                    if (LinearizeBoundary(boundary, poly))
                    {
                        // remove excess points
                        poly.eliminate_redundant_vertices(1.0);

                        // ensure that the polygon is simple
                        if (poly.is_simple(epsilon))
                        {
                            // ensure that the polygon is properly oriented
                            if (poly.area() < 0)
                                poly.reverse();

                            polygonsToShrink.push_back(poly);
                            shrinkValues.push_back(delta);
                        }
                    }
                }
            }
        }

        // add water zone
        VisiLibity::Polygon waterpoly;
        if (geom && LinearizeBoundary(geom, waterpoly))
        {
            // remove excess points
            waterpoly.eliminate_redundant_vertices(1.0);

            // ensure that the polygon is simple
            if (waterpoly.is_simple(epsilon))
            {
                // ensure that the polygon is properly oriented
                if (waterpoly.area() < 0)
                    waterpoly.reverse();

                polygonsToShrink.push_back(waterpoly);
                shrinkValues.push_back(0.0); // TODO: parameterize water zone padding
            }
        }

        // shrink all polygons
        std::vector< VisiLibity::Polygon > shrunkenPolygons;
        if (VisiLibity::Polygon::offset_polygons(polygonsToShrink, shrunkenPolygons, shrinkValues, epsilon))
        {
            if (!shrunkenPolygons.empty())
            {
                validKeepInZone = true;

                // add shrunken polygons to complete list
                for (size_t n = 0; n < shrunkenPolygons.size(); n++)
                {
                    // eliminate redundant vertices
                    shrunkenPolygons[n].eliminate_redundant_vertices(1.0);

                    // check orientation and reverse if necessary
                    if (shrunkenPolygons[n].area() < 0)
                        shrunkenPolygons[n].reverse();

                    // enforce standard form
                    shrunkenPolygons[n].enforce_standard_form();
                }

                // add largest keep-in polygon as the main boundary
                double maxarea = fabs(shrunkenPolygons[0].area());
                size_t maxindex = 0;
                for (size_t n = 1; n < shrunkenPolygons.size(); n++)
                {
                    double a = fabs(shrunkenPolygons[n].area());
                    if (a > maxarea)
                    {
                        maxarea = a;
                        maxindex = n;
                    }
                }
                polygonPlanningList.insert(polygonPlanningList.begin(), shrunkenPolygons[maxindex]);
            }
        }

        if (!validKeepInZone && boxInitialized)
        {
            VisiLibity::Polygon poly;
            VisiLibity::Point pt;

            // since no official keep-in boundary, pad by a large amount (50 km)
            pt.set_x(zoneBox.x_max + 50000);
            pt.set_y(zoneBox.y_max + 50000);
            poly.push_back(pt);

            pt.set_x(zoneBox.x_max + 50000);
            pt.set_y(zoneBox.y_min - 50000);
            poly.push_back(pt);

            pt.set_x(zoneBox.x_min - 50000);
            pt.set_y(zoneBox.y_min - 50000);
            poly.push_back(pt);

            pt.set_x(zoneBox.x_min - 50000);
            pt.set_y(zoneBox.y_max + 50000);
            poly.push_back(pt);

            if (poly.area() < 0)
                poly.reverse();
            poly.enforce_standard_form();
            polygonPlanningList.insert(polygonPlanningList.begin(), poly);
        }

        if (!polygonPlanningList.empty())
        {
            // create environment
            VisiLibity::Environment* environment = new VisiLibity::Environment(polygonPlanningList);

            // check for epsilon valid
            if (environment->is_valid(epsilon))
            {
                // save environment
                m_environments[region->getID()][vehicleId].reset(environment);
                // create visibility graph
                m_visgraphs[region->getID()][vehicleId].reset(new VisiLibity::Visibility_Graph(*environment, epsilon));
            }
            else
            {
                delete environment;
            }
        }
    }
}

bool RoutePlannerService::LinearizeBoundary(afrl::cmasi::AbstractGeometry* boundary, VisiLibity::Polygon& poly)
{
    uxas::common::utilities::CUnitConversions flatEarth;
    bool isValid = false;
    poly.clear();

    if (afrl::cmasi::isPolygon(boundary))
    {
        afrl::cmasi::Polygon* boundaryPolygon = (afrl::cmasi::Polygon*) boundary;
        for (unsigned int k = 0; k < boundaryPolygon->getBoundaryPoints().size(); k++)
        {
            VisiLibity::Point pt;
            double north, east;
            flatEarth.ConvertLatLong_degToNorthEast_m(boundaryPolygon->getBoundaryPoints()[k]->getLatitude(), boundaryPolygon->getBoundaryPoints()[k]->getLongitude(), north, east);
            pt.set_x(east);
            pt.set_y(north);
            poly.push_back(pt);
        }
        isValid = true;
    }
    else if (afrl::cmasi::isRectangle(boundary))
    {
        afrl::cmasi::Rectangle* rectangle = (afrl::cmasi::Rectangle*) boundary;
        VisiLibity::Point c;
        double north, east;
        flatEarth.ConvertLatLong_degToNorthEast_m(rectangle->getCenterPoint()->getLatitude(), rectangle->getCenterPoint()->getLongitude(), north, east);
        c.set_x(east);
        c.set_y(north);

        VisiLibity::Point pt;
        // note: north-aligned positive rotation is opposite direction of x-aligned positive rotation
        double a = -rectangle->getRotation() * n_Const::c_Convert::dDegreesToRadians();
        double w = rectangle->getWidth();
        double h = rectangle->getHeight();

        poly.push_back(VisiLibity::Point::rotate(VisiLibity::Point(east + w/2.0, north + h/2.0) - c, a) + c);
        poly.push_back(VisiLibity::Point::rotate(VisiLibity::Point(east - w/2.0, north + h/2.0) - c, a) + c);
        poly.push_back(VisiLibity::Point::rotate(VisiLibity::Point(east - w/2.0, north - h/2.0) - c, a) + c);
        poly.push_back(VisiLibity::Point::rotate(VisiLibity::Point(east + w/2.0, north - h/2.0) - c, a) + c);

        isValid = true;
    }
    else if (afrl::cmasi::isCircle(boundary))
    {
        afrl::cmasi::Circle* circle = (afrl::cmasi::Circle*) boundary;
        VisiLibity::Point c;
        double north, east;
        flatEarth.ConvertLatLong_degToNorthEast_m(circle->getCenterPoint()->getLatitude(), circle->getCenterPoint()->getLongitude(), north, east);
        c.set_x(east);
        c.set_y(north);
        double r = circle->getRadius() / cos(10.0 * n_Const::c_Convert::dDegreesToRadians());

        for (uint32_t k = 0; k < 18; k++)
        {
            VisiLibity::Point pt;
            pt.set_x(c.x() + r * cos(n_Const::c_Convert::dTwoPi() * k / 18.0));
            pt.set_y(c.y() + r * sin(n_Const::c_Convert::dTwoPi() * k / 18.0));
            poly.push_back(pt);
        }

        isValid = true;
    }

    return isValid;
}

std::shared_ptr<uxas::messages::route::RoutePlanResponse>
RoutePlannerService::HandleRoutePlanRequestMsg(std::shared_ptr<uxas::messages::route::RoutePlanRequest> request)
{
    uxas::common::utilities::CUnitConversions flatEarth;
    VisiLibity::Point vehiclePt;
    double speed = -1.0;
    double alt = 0.0;
    afrl::cmasi::AltitudeType::AltitudeType altType = afrl::cmasi::AltitudeType::MSL;

    int64_t regionId = request->getOperatingRegion();
    int64_t vehicleId = request->getVehicleID();
    int64_t taskId = request->getAssociatedTaskID();
    bool hasState = false;

    auto state = m_entityStates.find(vehicleId);
    if (state != m_entityStates.end())
    {
        double north, east;
        flatEarth.ConvertLatLong_degToNorthEast_m(state->second->getLocation()->getLatitude(), state->second->getLocation()->getLongitude(), north, east);
        vehiclePt.set_x(east);
        vehiclePt.set_y(north);
        speed = state->second->getGroundspeed();
        alt = state->second->getLocation()->getAltitude();
        altType = state->second->getLocation()->getAltitudeType();
        hasState = true;
    }

    auto config = m_entityConfigurations.find(vehicleId);
    if (config != m_entityConfigurations.end() && (!hasState || speed < 0.1))
    {
        speed = config->second->getNominalSpeed();
        alt = config->second->getNominalAltitude();
        altType = config->second->getNominalAltitudeType();
    }

    // plan for all the requests
    std::shared_ptr<uxas::messages::route::RoutePlanResponse> response(new uxas::messages::route::RoutePlanResponse);
    response->setResponseID(request->getRequestID());
    response->setAssociatedTaskID(taskId);
    response->setVehicleID(vehicleId);
    response->setOperatingRegion(regionId);
    for (size_t k = 0; k < request->getRouteRequests().size(); k++)
    {
        bool hasValidLocations = (speed < 1e-4) ? false : true;
        uxas::messages::route::RouteConstraints* routeRequest = request->getRouteRequests().at(k);
        int64_t routeId = routeRequest->getRouteID();
        VisiLibity::Point startPt, endPt;
        double north, east;

        uxas::messages::route::RoutePlan* plan = new uxas::messages::route::RoutePlan;
        plan->setRouteID(routeId);

        if (routeRequest->getStartLocation() == nullptr && hasState)
        {
            startPt = vehiclePt;
        }
        else if (routeRequest->getStartLocation() != nullptr)
        {
            flatEarth.ConvertLatLong_degToNorthEast_m(routeRequest->getStartLocation()->getLatitude(), routeRequest->getStartLocation()->getLongitude(), north, east);
            startPt.set_x(east);
            startPt.set_y(north);
        }
        else
        {
            hasValidLocations = false;
        }

        if (routeRequest->getEndLocation() == nullptr && hasState)
        {
            endPt = vehiclePt;
        }
        else if (routeRequest->getEndLocation() != nullptr)
        {
            flatEarth.ConvertLatLong_degToNorthEast_m(routeRequest->getEndLocation()->getLatitude(), routeRequest->getEndLocation()->getLongitude(), north, east);
            endPt.set_x(east);
            endPt.set_y(north);
        }
        else
        {
            hasValidLocations = false;
        }

        if (hasValidLocations)
        {
            bool hasEnvironment = false;
            auto r = m_environments.find(regionId);
            if (r != m_environments.end())
            {
                auto v = r->second.find(vehicleId);
                if (v != r->second.end())
                {
                    VisiLibity::Environment* env = v->second.get();

                    auto s = m_visgraphs.find(regionId);
                    if (s != m_visgraphs.end())
                    {
                        auto vv = s->second.find(vehicleId);
                        if (vv != s->second.end())
                        {
                            VisiLibity::Visibility_Graph* graph = vv->second.get();
                            hasEnvironment = true;

                            // make sure locations can be reached
                            if (startPt.in(*env, 1e-4) && endPt.in(*env, 1e-4))
                            {
                                VisiLibity::Polyline path = env->shortest_path(startPt, endPt, *graph, 1e-4);
                                // speed is guaranteed to be bounded postive away from zero by default setting on 'validLocations'
                                // alt and altType are valid by same logic
                                plan->setRouteCost((path.length() / speed * 1000)); // WARNING: in seconds -> change to miliseconds?? DONE RAS

                                if (!request->getIsCostOnlyRequest())
                                {
                                    afrl::cmasi::Waypoint* wp;
                                    for (size_t n = 0; n < path.size(); n++)
                                    {
                                        wp = new afrl::cmasi::Waypoint();
                                        double lat, lon;
                                        flatEarth.ConvertNorthEast_mToLatLong_deg(path[n].y(), path[n].x(), lat, lon);
                                        wp->setLatitude(lat);
                                        wp->setLongitude(lon);
                                        wp->setAltitude(alt);
                                        wp->setAltitudeType(altType);
                                        wp->setNumber(n + 1);
                                        wp->setNextWaypoint(n + 2);
                                        if ((n + 1) >= path.size())
                                        {
                                            wp->setNextWaypoint(n + 1);
                                        }
                                        wp->setSpeed(speed);
                                        wp->setTurnType(afrl::cmasi::TurnType::TurnShort);
                                        plan->getWaypoints().push_back(wp);
                                    }
                                }
                            }
                        }
                    }
                }
            }

            if (!hasEnvironment)
            {
                // no valid region, so straight line plan
                double linedist = VisiLibity::distance(startPt, endPt);
                plan->setRouteCost((linedist / speed * 1000)); // WARNING: in seconds -> change to miliseconds?? DONE: RAS

                if (!request->getIsCostOnlyRequest())
                {
                    afrl::cmasi::Waypoint* wp;
                    double lat, lon;

                    wp = new afrl::cmasi::Waypoint();
                    flatEarth.ConvertNorthEast_mToLatLong_deg(startPt.y(), startPt.x(), lat, lon);
                    wp->setLatitude(lat);
                    wp->setLongitude(lon);
                    wp->setAltitude(alt);
                    wp->setAltitudeType(altType);
                    wp->setNumber(1);
                    wp->setNextWaypoint(2);
                    wp->setSpeed(speed);
                    wp->setTurnType(afrl::cmasi::TurnType::TurnShort);
                    plan->getWaypoints().push_back(wp);

                    wp = new afrl::cmasi::Waypoint();
                    flatEarth.ConvertNorthEast_mToLatLong_deg(endPt.y(), endPt.x(), lat, lon);
                    wp->setLatitude(lat);
                    wp->setLongitude(lon);
                    wp->setAltitude(alt);
                    wp->setAltitudeType(altType);
                    wp->setNumber(2);
                    wp->setNextWaypoint(2);
                    wp->setSpeed(speed);
                    wp->setTurnType(afrl::cmasi::TurnType::TurnShort);
                    plan->getWaypoints().push_back(wp);
                }
            }
        }

        response->getRouteResponses().push_back(plan);
    }

    return response;
}

}; //namespace service
}; //namespace uxas

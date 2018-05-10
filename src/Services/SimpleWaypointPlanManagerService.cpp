// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   SimpleWaypointPlanManagerService.cpp
 * Author: derek
 *
 * Created on December 1, 2017
 *
 */


#include "SimpleWaypointPlanManagerService.h"

#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/vehicles/SurfaceVehicleConfiguration.h"

#include "UnitConversions.h"

#define STRING_XML_VEHICLE_ID "VehicleID"

namespace uxas
{
namespace service
{
SimpleWaypointPlanManagerService::ServiceBase::CreationRegistrar<SimpleWaypointPlanManagerService>
SimpleWaypointPlanManagerService::s_registrar(SimpleWaypointPlanManagerService::s_registryServiceTypeNames());

SimpleWaypointPlanManagerService::SimpleWaypointPlanManagerService()
: ServiceBase(SimpleWaypointPlanManagerService::s_typeName(), SimpleWaypointPlanManagerService::s_directoryName()) { };

SimpleWaypointPlanManagerService::~SimpleWaypointPlanManagerService() { };

bool
SimpleWaypointPlanManagerService::configure(const pugi::xml_node& ndComponent)
{
    m_vehicleID = m_entityId;
    if (!ndComponent.attribute(STRING_XML_VEHICLE_ID).empty())
    {
        m_vehicleID = ndComponent.attribute(STRING_XML_VEHICLE_ID).as_uint();
    }
    
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);

    // ENTITY CONFIGURATIONS
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
    for(auto child : childconfigs)
        addSubscriptionAddress(child);

    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);
    
    return true;
}

bool
SimpleWaypointPlanManagerService::initialize()
{
    return true;
};

bool
SimpleWaypointPlanManagerService::terminate()
{
    return true;
}

bool
SimpleWaypointPlanManagerService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
    auto entityConfig = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);

    if(entityState)
    {
        m_states[entityState->getID()] = entityState;
    }
    else if(entityConfig)
    {
        m_configs[entityConfig->getID()] = entityConfig;
    }
    else if (afrl::cmasi::isAutomationResponse(receivedLmcpMessage->m_object))
    {
        auto automationResponse = std::static_pointer_cast<afrl::cmasi::AutomationResponse> (receivedLmcpMessage->m_object);
        for (auto mission : automationResponse->getMissionCommandList())
        {
            if (mission->getVehicleID() == m_vehicleID)
            {
                std::shared_ptr<afrl::cmasi::MissionCommand> mish(mission->clone());
                if(mish->getWaypointList().size() == 1)
                {
                    handleSingleWaypointPlan(mish);
                }
                sendSharedLmcpObjectBroadcastMessage(mish);
                break;
            }
        }
    }
    
    return (false); // always false implies never terminating service from here
};

void SimpleWaypointPlanManagerService::handleSingleWaypointPlan(std::shared_ptr<afrl::cmasi::MissionCommand>& mish)
{
    // pre-condition: at least one waypoint in the plan
    if(mish->getWaypointList().empty()) return;

    // default values of min turn radius and heading along path to waypoint
    double R = 30000;
    double heading = 0.0;

    // calculate turn radius from configuration
    if(m_configs.find(m_vehicleID) != m_configs.end())
    {
        // R = V^2/tan(phi)/g
        double V = m_configs[m_vehicleID]->getNominalSpeed();
        double phi = 45.0; // default assumption vehicles without bank angle considerations
        auto avconfig = std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(m_configs[m_vehicleID]);
        auto svconfig = std::dynamic_pointer_cast<afrl::vehicles::SurfaceVehicleConfiguration>(m_configs[m_vehicleID]);
        if(avconfig)
        {
            phi = avconfig->getNominalFlightProfile()->getMaxBankAngle();
        }
        if(svconfig)
        {
            phi = svconfig->getMaxBankAngle();
        }
        
        // make sure max bank angle is reasonable (i.e. must be postive between 1 .. 89)
        phi = fabs(phi);
        if(phi < 1.0) phi = 1.0;
        if(phi > 89.0) phi = 89.0;

        // convert max bank angle to radians
        phi = phi*n_Const::c_Convert::dDegreesToRadians();

        // calculate minimum turn radius
        R = V*V/(9.80665*tan(phi));
    }

    // convert to local coordinates
    uxas::common::utilities::CUnitConversions flatEarth;
    double north, east;
    flatEarth.ConvertLatLong_degToNorthEast_m(mish->getWaypointList().back()->getLatitude(), mish->getWaypointList().back()->getLongitude(), north, east);

    // determine heading
    if(m_states.find(m_vehicleID) != m_states.end())
    {
        double pos_north, pos_east;
        flatEarth.ConvertLatLong_degToNorthEast_m(m_states[m_vehicleID]->getLocation()->getLatitude(), m_states[m_vehicleID]->getLocation()->getLongitude(), pos_north, pos_east);
        heading = atan2(east - pos_east, north - pos_north);
    }

    auto wp = mish->getWaypointList().back()->clone();
    mish->getWaypointList().back()->setNextWaypoint(mish->getWaypointList().back()->getNumber()+1);
    wp->setNumber(mish->getWaypointList().back()->getNumber()+1);

    // project next location out by 2*R along vector from current position to destination
    north += 2*R*cos(heading);
    east += 2*R*sin(heading);
    double lat, lon;
    flatEarth.ConvertNorthEast_mToLatLong_deg(north, east, lat, lon);
    wp->setLatitude(lat);
    wp->setLongitude(lon);

    mish->getWaypointList().push_back(wp);
}

}; //namespace service
}; //namespace uxas

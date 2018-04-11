// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   SimpleWaypointPlanManagerService.h
 * Author: derek
 *
 * Created on December 1, 2017
 */

#ifndef UXAS_SERVICE_SIMPLE_WAYPOINT_PLAN_MANAGER_SERVICE_H
#define UXAS_SERVICE_SIMPLE_WAYPOINT_PLAN_MANAGER_SERVICE_H

#include "ServiceBase.h"

#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/MissionCommand.h"

#include <unordered_map>
#include <cstdint> // uint32_t

namespace uxas
{
namespace service
{


/*! \class SimpleWaypointPlanManagerService
 *  \brief A service that serves complete plans to a vehicle interface.
 *
 * 1) Receive AutomationResponse
 * 2) Find MissionCommand for the configured ID 
 * 3) Send only that mission command for the configured vehicle
 * 
 * Configuration String: 
 *  <Service Type="SimpleWaypointPlanManagerService" VehicleID="100" />
 * 
 * Options:
 *  - VehicleID
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::AutomationResponse
 *  - afrl::cmasi::EntityConfiguration
 *  - afrl::cmasi::EntityState
 * 
 * Sent Messages:
 *  - afrl::cmasi::MissionCommand
 * 
 */



class SimpleWaypointPlanManagerService : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("SimpleWaypointPlanManagerService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName()
    {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create()
    {
        return new SimpleWaypointPlanManagerService;
    };

    SimpleWaypointPlanManagerService();

    virtual
    ~SimpleWaypointPlanManagerService();

private:

    static
    ServiceBase::CreationRegistrar<SimpleWaypointPlanManagerService> s_registrar;

    /** brief Copy construction not permitted */
    SimpleWaypointPlanManagerService(SimpleWaypointPlanManagerService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(SimpleWaypointPlanManagerService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    //bool
    //start() override;

    bool
    terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

    /*! \brief  special case handling for situations where plan consists of a single waypoint */
    void handleSingleWaypointPlan(std::shared_ptr<afrl::cmasi::MissionCommand>& mish);

    /*! \brief  ID of the vehicle that this manager is working for */
    int64_t m_vehicleID = {-1}; // need a vehicle ID or can't do anything

    /*! \brief  local tracking of all entity configurations in the system (used for max-bank angle for min turn radius calculation) */
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration> > m_configs;

    /*! \brief  local tracking of all entity states in the system (used for position for heading calculation) */
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_states;

};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_SIMPLE_WAYPOINT_PLAN_MANAGER_SERVICE_H */


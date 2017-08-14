// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_RoutePlanner.h
 * Author: derek
 *
 * Created on Aug 2, 2015, 8:21 AM
 */



#ifndef UXAS_SERVICE_ROUTE_PLANNER_SERVICE_H
#define UXAS_SERVICE_ROUTE_PLANNER_SERVICE_H

#include "ServiceBase.h"
#include "afrl/cmasi/CMASI.h"
#include "uxas/messages/route/ROUTE.h"
#include "afrl/impact/IMPACT.h"
#include "afrl/vehicles/VEHICLES.h"
#include "visilibity.h"

#include <unordered_map>
#include <unordered_set>
#include <cstdint>

namespace uxas
{
namespace service
{

/*! \class RoutePlannerService
    \brief A component that responds to route plan requests. Uses
 *  the library 'DubLib' for air and surface entities. Does not respond
 *  to requests involving ground entities (assumes a ground planner
 *  will plan for ground entities).
 * 
 * Configuration String: 
 * 
 * Options:
 *  - 
 * 
 * Subscribed Messages:
 *  - 
 * 
 * Sent Messages:
 *  - 
 * 
 */


class RoutePlannerService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("RoutePlannerService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create() {
        return new RoutePlannerService;
    };

    RoutePlannerService();

    virtual
    ~RoutePlannerService();

private:

    static
    ServiceBase::CreationRegistrar<RoutePlannerService> s_registrar;

    /** brief Copy construction not permitted */
    RoutePlannerService(RoutePlannerService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(RoutePlannerService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    //bool
    //initialize() override;

    //bool
    //start() override;

    //bool
    //terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


public:




public: //virtual






private:




    std::shared_ptr<uxas::messages::route::RoutePlanResponse> HandleRoutePlanRequestMsg(std::shared_ptr<uxas::messages::route::RoutePlanRequest>);
    void BuildVisibilityRegion(std::shared_ptr<afrl::cmasi::OperatingRegion>);
    void UpdateRegions(std::shared_ptr<avtas::lmcp::Object>);
    void BuildVehicleSpecificRegion(std::shared_ptr<afrl::cmasi::OperatingRegion>, int64_t, afrl::cmasi::AbstractGeometry*);
    bool LinearizeBoundary(afrl::cmasi::AbstractGeometry*, VisiLibity::Polygon&);

    // storage
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_entityStates;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration> > m_entityConfigurations;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::KeepInZone> > m_keepInZones;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::KeepOutZone> > m_keepOutZones;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::OperatingRegion> > m_operatingRegions;
    std::unordered_set<int64_t> m_airVehicles;
    std::unordered_set<int64_t> m_groundVehicles;
    std::unordered_set<int64_t> m_surfaceVehicles;
    std::unordered_map<int64_t, std::shared_ptr<afrl::impact::WaterZone> > m_waterZones;

    // environments for all vehicles that will have plans
    // [operating region id], [vehicle id], <environment/graph>
    std::unordered_map<int64_t, std::unordered_map<int64_t, std::shared_ptr<VisiLibity::Environment> > > m_environments;
    std::unordered_map<int64_t, std::unordered_map<int64_t, std::shared_ptr<VisiLibity::Visibility_Graph> > > m_visgraphs;

};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_ROUTE_PLANNER_SERVICE_H */

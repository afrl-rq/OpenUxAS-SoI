// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_RoutePlannerVisibility.h
 * Author: steve
 *
 * Created on February 19, 2015, 4:47 PM
 */


#ifndef UXAS_SERVICE_ROUTE_PLANNER_VISIBILITY_SERVICE_H
#define UXAS_SERVICE_ROUTE_PLANNER_VISIBILITY_SERVICE_H


#include "VisibilityGraph.h"

#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RoutePlanRequest.h"
#include "uxas/messages/route/RouteResponse.h"
#include "uxas/messages/route/RoutePlanResponse.h"

#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/OperatingRegion.h"


#include "ServiceBase.h"


namespace uxas
{
namespace service
{

/*! \class RoutePlannerVisibilityService
    \brief A component that constructs plans/costs to be used for assignments.

 * 1) Receive KeepInZones/KeepOutZones/Tasks/RoutePlanRequests
 * 2) Build/Maintain Base Visibility Graph (Euclidean) from KeepInZones/KeepOutZones
 * 3) ???Construct, and send out, a RoutePlanResponse which includes minimum
 *    path lengths from each vehicle to each task and from each task to every other task.?????
 * 4) ???Construct, and send out, a ???Response which includes minimum waypoint paths
 *    paths for each plan request.?????
 * 
 * Configuration String: 
 *  <Service Type="RoutePlannerVisibilityService" TurnRadiusOffset_m="0.0" 
  *                OsmFileName="" MinimumWaypointSeparation_m="50.0"/> 
 * 
 * Options:
 *  - TurnRadiusOffset_m
 *  - OsmFileName
 *  - MinimumWaypointSeparation_m
 *  - 
 *  - 
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::KeepOutZone
 *  - afrl::cmasi::KeepInZone
 *  - afrl::cmasi::OperatingRegion
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - afrl::vehicles::SurfaceVehicleConfiguration
 *  - uxas::messages::route::RoutePlanRequest
 *  - AircraftPathPlanner
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::vehicles::GroundVehicleState
 *  - afrl::vehicles::SurfaceVehicleState
 *  - uxas::messages::route::RouteRequest
 * 
 * Sent Messages:
 *  - uxas::messages::route::RoutePlanResponse
 * 
 */




class RoutePlannerVisibilityService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("RoutePlannerVisibilityService");
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
        return new RoutePlannerVisibilityService;
    };

    RoutePlannerVisibilityService();

    virtual
    ~RoutePlannerVisibilityService();

private:

    static
    ServiceBase::CreationRegistrar<RoutePlannerVisibilityService> s_registrar;

    /** brief Copy construction not permitted */
    RoutePlannerVisibilityService(RoutePlannerVisibilityService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(RoutePlannerVisibilityService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    //bool
    //start() override;

    //bool
    //terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


public:



public: //virtual





public:

protected:
    bool bProcessZone(const std::shared_ptr<afrl::cmasi::AbstractZone>& abstractZone, const bool& isKeepIn);
    bool bProcessOperatingRegion(const std::shared_ptr<afrl::cmasi::OperatingRegion>& operatingRegion);
    bool bProcessRouteRequest(const std::shared_ptr<uxas::messages::route::RouteRequest>& routeRequest);
    bool bProcessRoutePlanRequest(const std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest,
            std::shared_ptr<uxas::messages::route::RoutePlanResponse>& routePlanResponse);
    bool bFindPointsForAbstractGeometry(afrl::cmasi::AbstractGeometry* pAbstractGeometry, n_FrameworkLib::V_POSITION_t& vposBoundaryPoints);
    bool isCalculateWaypoints(const n_FrameworkLib::PTR_VISIBILITYGRAPH_t& visibilityGraph,
            const std::shared_ptr<n_FrameworkLib::CPathInformation>& pathInformation,
            const int64_t& vehicleId, const double& startHeading_deg, const double& endHeading_deg,
            std::vector<afrl::cmasi::Waypoint*>& planWaypoints,const n_FrameworkLib::CTrajectoryParameters::enPathType_t& enpathType);
    void calculatePlannerParameters(const std::shared_ptr<afrl::cmasi::EntityConfiguration>& enityConfiguration);

public:

    struct s_PlannerParameters
    {
        double turnRadius_m = {0};
        double nominalSpeed_mps = {0};
    };


protected:

    /*! \brief  storage for vehicle configurations*/
    std::map<uint64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration>> m_idVsEntityConfiguration;
    /*! \brief  this is where vehicle states are stored*/
    std::map<uint64_t, std::shared_ptr<afrl::cmasi::EntityState>> m_idVsEntityState;
    /*! \brief  this is where planner parameters for each vehicle are stored*/
    std::map<uint64_t, std::shared_ptr<s_PlannerParameters>> m_idVsPlannerParameters;

    /*! \brief  storage for the "processed" keep-in/keep-out boundaries*/
    n_FrameworkLib::M_UI64_PTR_BOUNDARY_t m_idVsBoundary;
    /*! \brief  storage for operating region visibility graphs */
    std::map<int64_t, n_FrameworkLib::PTR_VISIBILITYGRAPH_t> m_operatingIdVsBaseVisibilityGraph;
    /*! \brief  storage for an openstreetmap based visibility graph */
    n_FrameworkLib::PTR_VISIBILITYGRAPH_t m_osmBaseVisibilityGraph;

    /*! \brief  this value is added to the run radius value for all vehicles.*/
    double m_turnRadiusOffset_m{0.0};

    /*! \brief  when this is set to true, the component will act both as a RouteAggregator and a RoutePlanner.*/
    bool m_isRoutAggregator{false};

    /*! \brief  //TODO:: Still needed????// storage for path planner results, saved for each vehicle ID*/
    //std::map<uint64_t,n_FrameworkLib::PTR_M_INT_PTR_M_INT_PATHINFORMATION_t> m_vehicleIdVsPlannerResults;

    double m_minimumWaypointSeparation_m = 50; //TODO:: this need to be configurable

private:




};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_ROUTE_PLANNER_VISIBILITY_SERVICE_H */


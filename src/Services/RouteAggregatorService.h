// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_RouteAggregator.h
 * Author: derek
 *
 * Created on Aug 2, 2015, 8:21 AM
 */



#ifndef UXAS_SERVICE_ROUTE_AGGREGATOR_SERVICE_H
#define UXAS_SERVICE_ROUTE_AGGREGATOR_SERVICE_H

#include "ServiceBase.h"
#include "afrl/cmasi/CMASI.h"
#include "afrl/impact/IMPACT.h"
#include "afrl/vehicles/VEHICLES.h"
#include "uxas/messages/route/ROUTE.h"
#include "uxas/messages/task/UXTASK.h"

#include "visilibity.h"

#include <memory>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <cstdint>

namespace uxas
{
namespace service
{
// description of a particular (task+option) to (task+option) 

class AggregatorTaskOptionPair
{
public:

    AggregatorTaskOptionPair() { };

    AggregatorTaskOptionPair(int64_t v, int64_t pt, int64_t pto, int64_t t, int64_t to) {
        vehicleId = v;
        prevTaskId = pt;
        prevTaskOption = pto;
        taskId = t;
        taskOption = to;
    };

    ~AggregatorTaskOptionPair() { };

    int64_t vehicleId{0};
    int64_t taskId{0};
    int64_t taskOption{0};
    int64_t prevTaskId{0};
    int64_t prevTaskOption{0};
};


/*! \class RouteAggregatorService
    \brief A component that incrementally queries the route planner to build
 *   a matrix of plans between all tasks and entity initial points 

 * 
 * Configuration String: 
 *  <Service Type="RouteAggregatorService" FastPlan="FALSE" />
 * 
 * Options:
 *  - FastPlan
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::vehicles::GroundVehicleState
 *  - afrl::vehicles::SurfaceVehicleState
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - afrl::vehicles::SurfaceVehicleConfiguration
 *  - uxas::messages::task::UniqueAutomationRequest
 *  - uxas::messages::task::TaskPlanOptions
 *  - uxas::messages::route::RouteRequest
 *  - uxas::messages::route::RoutePlanResponse
 *  - 
 *  - 
 *  - 
 *  - 
 * 
 * Sent Messages:
 *  - uxas::messages::route::RoutePlanRequest
 *  - GroundPathPlanner
 *  - AircraftPathPlanner
 *  - uxas::messages::route::RouteResponse
 *  - uxas::messages::task::AssignmentCostMatrix
 *  - afrl::cmasi::ServiceStatus
 * 
 */

class RouteAggregatorService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("RouteAggregatorService");
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
        return new RouteAggregatorService;
    };

    RouteAggregatorService();

    virtual
    ~RouteAggregatorService();

private:

    static
    ServiceBase::CreationRegistrar<RouteAggregatorService> s_registrar;

    /** brief Copy construction not permitted */
    RouteAggregatorService(RouteAggregatorService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(RouteAggregatorService const&) = delete;

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






private:




    void HandleRouteRequest(std::shared_ptr<uxas::messages::route::RouteRequest>);
    void EuclideanPlan(std::shared_ptr<uxas::messages::route::RoutePlanRequest>);
    void CheckAllTaskOptionsReceived();
    void CheckAllRoutePlans();
    void BuildMatrixRequests(int64_t, const std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>&);
    void SendRouteResponse(int64_t);
    void SendMatrix(int64_t);

    // Configurable parameter that disables potentially costly ground route calculations
    // Paramter is identified as 'FastPlan' in the configuration file
    // Fast planning ignores all environment and dynamic constraints and plans straight line only
    bool m_fastPlan{false};

    // vehicle state and configuration storage
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_entityStates;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration> > m_entityConfigurations;
    std::unordered_set<int64_t> m_airVehicles;
    std::unordered_set<int64_t> m_groundVehicles;
    std::unordered_set<int64_t> m_surfaceVehicles;

    // Store all AutomationRequests and SandboxAutomationRequests to ensure that each request
    // gets a response in the form of an AssignmentCostMatrix
    int64_t m_autoRequestId{1}; // FUTURE: use ID from 'AutomationRequest' itself [requires CMASI change]
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> > m_uniqueAutomationRequests;

    // Each task returns a single set of task options as 'TaskPlanOptions'
    // Store these with key value of task ID
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::task::TaskPlanOptions> > m_taskOptions;

    // Lower-level route planners are sent the proper requests to build a response to fulfill either a
    // 'RouteRequest' or an 'AutomationRequest'. The following data structures indicate the route ID for
    // each low-level request to match it with the returned route plan. When all pending route plans are
    // received, then a final high-level response is sent (in terms of a 'RouteResponse' or 'AssignmentCostMatrix')

    // Starting ID for uniquely identifying route plan
    int64_t m_routeId{1000000}; // start outside of any task or waypoint id
    //                route id,    plan response id                 returned route plan
    std::unordered_map<int64_t, std::pair<int64_t, std::shared_ptr<uxas::messages::route::RoutePlan> > > m_routePlans;

    // Set of route IDs that correspond to an original high-level request
    //             autoRequestID                  route ID
    std::unordered_map<int64_t, std::unordered_set<int64_t> > m_pendingAutoReq;

    // Mapping from route ID to the corresponding task/option pair
    //                route id,      task+option pair
    std::unordered_map<int64_t, std::shared_ptr<AggregatorTaskOptionPair> > m_routeTaskPairing;


    // Track full route plan responses for directly reconstructing 'RouteResponse'
    int64_t m_routeRequestId{1};
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::route::RoutePlanResponse> > m_routePlanResponses;

    // Set of route plan response IDs that correspond to an original high-level request
    //            routeRequestID     expected plan response IDs
    std::unordered_map<int64_t, std::unordered_set<int64_t> > m_pendingRoute;
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_ROUTE_AGGREGATOR_SERVICE_H */

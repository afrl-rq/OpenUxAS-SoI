// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_BatchSummary.h
 * Author: derek
 *
 * Created on Oct 25, 2015, 3:56 PM
 */



#ifndef UXAS_SERVICE_BATCH_SUMMARY_SERVICE_H
#define UXAS_SERVICE_BATCH_SUMMARY_SERVICE_H

#include "ServiceBase.h"
#include "afrl/cmasi/CMASI.h"
#include "afrl/impact/IMPACT.h"
#include "afrl/vehicles/VEHICLES.h"
#include "uxas/messages/route/ROUTE.h"

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

/*! \class BatchSummaryService
    \brief A component that incrementally queries the route planner to build
 *   a matrix of plans between all tasks and entity initial points 
 * 
 * Configuration String: 
*  <Service Type="BatchSummaryService" FastPlan="FALSE" LaneSpacing="300.0" />
 * 
 * Options:
 *  - FastPlan
 *  - LaneSpacing
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::EntityConfiguration
 *  - afrl::impact::RadioTowerConfiguration
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - afrl::vehicles::SurfaceVehicleConfiguration
 *  - afrl::cmasi::EntityState
 *  - afrl::impact::RadioTowerState
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::vehicles::GroundVehicleState
 *  - afrl::vehicles::SurfaceVehicleState
 * 
 * Sent Messages:
 *  - afrl::impact::BatchSummaryResponse
 * 
 */


class BatchSummaryService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("BatchSummaryService");
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
        return new BatchSummaryService;
    };

    BatchSummaryService();

    virtual
    ~BatchSummaryService();

private:

    static
    ServiceBase::CreationRegistrar<BatchSummaryService> s_registrar;

    /** brief Copy construction not permitted */
    BatchSummaryService(BatchSummaryService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(BatchSummaryService const&) = delete;

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




    void HandleTaskMsg(std::shared_ptr<afrl::cmasi::Task>);
    void HandleBatchSummaryRequest(std::shared_ptr<afrl::impact::BatchSummaryRequest>);
    void HandleRoutePlanResponse(std::shared_ptr<uxas::messages::route::RoutePlanResponse>);
    void HandleEgressRouteResponse(std::shared_ptr<uxas::messages::route::EgressRouteResponse>);
    void AddPlanningPointsFromArea(int64_t, std::shared_ptr<afrl::cmasi::AbstractGeometry>);
    void AddCorners(int64_t, std::vector<VisiLibity::Point>&);
    void EuclideanPlan(std::shared_ptr<uxas::messages::route::RoutePlanRequest>);
    void UpdateSummary(afrl::impact::VehicleSummary*, uxas::messages::route::RoutePlan*);
    bool FinalizeBatchRequest(int64_t);
    void BuildSummaryOptions(int64_t, std::shared_ptr<afrl::impact::BatchSummaryResponse>&, std::vector<std::shared_ptr<afrl::impact::VehicleSummary> >&, int64_t);

    // task length calculations
    float PatternLength(std::shared_ptr<afrl::impact::PatternSearchTask>);
    float LineSearchLength(std::vector<afrl::cmasi::Location3D*>&);
    float AreaSearchLength(std::shared_ptr<afrl::cmasi::AbstractGeometry>);

    // parameters
    bool m_fastPlan{false};
    float m_laneSpacing{300.0f};

    // storage
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_entityStates;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration> > m_entityConfigs;
    std::unordered_set<int64_t> m_airVehicles;
    std::unordered_set<int64_t> m_groundVehicles;
    std::unordered_set<int64_t> m_surfaceVehicles;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::Task> > m_tasks;
    std::unordered_set<int64_t> m_multiVehicleTasks;
    std::unordered_map<int64_t, std::vector<std::shared_ptr<afrl::cmasi::Location3D> > > m_taskLocations;
    std::unordered_map<int64_t, std::pair<int64_t, float> > m_taskLengths; // taskId, timing, length
    std::unordered_map<int64_t, std::shared_ptr<afrl::impact::AreaOfInterest> > m_areasOfInterest;
    std::unordered_map<int64_t, std::shared_ptr<afrl::impact::LineOfInterest> > m_linesOfInterest;
    std::unordered_map<int64_t, std::shared_ptr<afrl::impact::PointOfInterest> > m_pointsOfInterest;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::Location3D> > m_towerLocations;
    std::unordered_map<int64_t, std::pair<float, bool> > m_towerRanges;

    //        task ID
    std::deque<int64_t> m_pendingEgressRequests;
    //                task ID
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::route::EgressRouteResponse> > m_egressPoints;

    int64_t m_responseId{1}; // internal tracking of numerous batch requests
    //               response id,             partial response
    std::unordered_map<int64_t, std::shared_ptr<afrl::impact::BatchSummaryResponse> > m_workingResponse;
    std::unordered_set<int64_t> m_readyResponse;

    int64_t m_routeId{5000000}; // start outside of any task or waypoint id
    //                route id,                   returned response
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::route::RoutePlanResponse> > m_routeResponses;
    //                route id, response id
    std::unordered_map<int64_t, int64_t> m_pendingRouteResponses;
    //                route id,         vehicle id, task id, prev task id
    std::unordered_map<int64_t, std::tuple<int64_t, int64_t, int64_t> > m_routeTaskPairing;
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_BATCH_SUMMARY_SERVICE_H */

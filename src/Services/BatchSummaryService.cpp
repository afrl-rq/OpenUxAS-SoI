// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_BatchSummary.cpp
 * Author: derek
 * 
 * Created on Oct 25, 2015, 3:56 PM
 */

#include "BatchSummaryService.h"

#include "UxAS_Log.h"
#include "pugixml.hpp"
#include "UnitConversions.h"
#include "DRand.h"
#include "Constants/Convert.h"
#include "Permute.h"
#include "Constants/UxAS_String.h"

#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/TaskDescendants.h"     

#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"


#include <map>
#include <numeric>

#define STRING_COMPONENT_NAME "BatchSummary"
#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME
#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_FAST_PLAN "FastPlan"
#define STRING_XML_LANE_SPACING "LaneSpacing"

// functor called for each permutation

class f
{
    afrl::impact::TaskSummary* tsum;
    afrl::impact::TaskSummary* orig;
    std::shared_ptr<afrl::impact::BatchSummaryResponse>& response;
    std::vector<std::shared_ptr<afrl::impact::VehicleSummary> >& vehicles;
public:

    explicit f(afrl::impact::TaskSummary* t,
            std::vector<std::shared_ptr<afrl::impact::VehicleSummary> >& v,
            std::shared_ptr<afrl::impact::BatchSummaryResponse>& r) : tsum(nullptr), orig(t), response(r), vehicles(v)
    {
    }

    template <class It>
    bool operator()(It first, It last) // called for each permutation
    {
        if (first != last)
        {
            tsum = orig->clone();
            for (; first != last; first++)
            {
                tsum->getPerformingVehicles().push_back(vehicles.at(*first)->clone());
            }
            response->getSummaries().push_back(tsum);
            tsum = nullptr;
        }
        return false;
    }
};

namespace uxas
{
namespace service
{
BatchSummaryService::ServiceBase::CreationRegistrar<BatchSummaryService>
BatchSummaryService::s_registrar(BatchSummaryService::s_registryServiceTypeNames());

BatchSummaryService::BatchSummaryService()
: ServiceBase(BatchSummaryService::s_typeName(), BatchSummaryService::s_directoryName())
{
};

BatchSummaryService::~BatchSummaryService()
{
};

bool
BatchSummaryService::initialize()
{

    return true;
}

bool
BatchSummaryService::configure(const pugi::xml_node & ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();

    std::string strFastPlan = ndComponent.attribute(STRING_XML_FAST_PLAN).value();
    if (!strFastPlan.empty())
    {
        m_fastPlan = ndComponent.attribute(STRING_XML_FAST_PLAN).as_bool();
    }

    std::string strLaneSpacing = ndComponent.attribute(STRING_XML_LANE_SPACING).value();
    if (!strLaneSpacing.empty())
    {
        m_laneSpacing = ndComponent.attribute(STRING_XML_LANE_SPACING).as_float();
        if (m_laneSpacing < 1.0f)
        {
            m_laneSpacing = 300.0f;
        }
    }


    // track states for watch task location prediction
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    addSubscriptionAddress(afrl::impact::RadioTowerConfiguration::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
    addSubscriptionAddress(afrl::vehicles::GroundVehicleConfiguration::Subscription);
    addSubscriptionAddress(afrl::vehicles::SurfaceVehicleConfiguration::Subscription);
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    addSubscriptionAddress(afrl::impact::RadioTowerState::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(afrl::vehicles::GroundVehicleState::Subscription);
    addSubscriptionAddress(afrl::vehicles::SurfaceVehicleState::Subscription);

    addSubscriptionAddress(afrl::impact::AreaOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::LineOfInterest::Subscription);
    addSubscriptionAddress(afrl::impact::PointOfInterest::Subscription);

    // Subscribe to Task and all derivatives of Task
    addSubscriptionAddress(afrl::cmasi::Task::Subscription);
    std::vector< std::string > childtasks = afrl::cmasi::TaskDescendants();
    for(auto child : childtasks)
        addSubscriptionAddress(child);

    // Primary messages for actual route construction
    addSubscriptionAddress(afrl::impact::BatchSummaryRequest::Subscription);
    addSubscriptionAddress(uxas::messages::route::RoutePlanResponse::Subscription);
    addSubscriptionAddress(uxas::messages::route::EgressRouteResponse::Subscription);

    // Subscribe to group messages


    return true; // may not have the proper fast plan value, but proceed anyway
}

bool
BatchSummaryService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    if (uxas::messages::route::isRoutePlanResponse(receivedLmcpMessage->m_object.get()))
    {
        HandleRoutePlanResponse(std::static_pointer_cast<uxas::messages::route::RoutePlanResponse>(receivedLmcpMessage->m_object));
    }
    else if (uxas::messages::route::isEgressRouteResponse(receivedLmcpMessage->m_object.get()))
    {
        HandleEgressRouteResponse(std::static_pointer_cast<uxas::messages::route::EgressRouteResponse>(receivedLmcpMessage->m_object));
    }
    else if (afrl::impact::isBatchSummaryRequest(receivedLmcpMessage->m_object.get()))
    {
        HandleBatchSummaryRequest(std::static_pointer_cast<afrl::impact::BatchSummaryRequest>(receivedLmcpMessage->m_object));
    }
    else if (std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object))
    {
        auto config = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        int64_t id = config->getID();
        m_entityConfigs[id] = config;

        if (afrl::impact::isRadioTowerConfiguration(receivedLmcpMessage->m_object.get()))
        {
            auto rconfig = std::static_pointer_cast<afrl::impact::RadioTowerConfiguration>(receivedLmcpMessage->m_object);
            int64_t id = rconfig->getID();
            m_towerLocations[id] = std::shared_ptr<afrl::cmasi::Location3D>(rconfig->getPosition()->clone());
            m_towerRanges[id] = std::make_pair(rconfig->getRange(), rconfig->getEnabled());
        }
    }
    else if (afrl::cmasi::isEntityState(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
        m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
    }
    else if (afrl::impact::isRadioTowerState(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
        m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        m_towerLocations[id] = std::shared_ptr<afrl::cmasi::Location3D>(m_entityStates[id]->getLocation()->clone());
        auto rs = std::static_pointer_cast<afrl::impact::RadioTowerState>(receivedLmcpMessage->m_object);
        if (m_towerRanges.find(id) != m_towerRanges.end())
        {
            m_towerRanges[id].second = rs->getEnabled();
        }
    }
    else if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
        m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        m_airVehicles.insert(id);
    }
    else if (afrl::vehicles::isGroundVehicleState(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
        m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        m_groundVehicles.insert(id);
    }
    else if (afrl::vehicles::isSurfaceVehicleState(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
        m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        m_surfaceVehicles.insert(id);
    }
    else if (afrl::impact::isPointOfInterest(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::impact::PointOfInterest>(receivedLmcpMessage->m_object)->getPointID();
        m_pointsOfInterest[id] = std::static_pointer_cast<afrl::impact::PointOfInterest>(receivedLmcpMessage->m_object);
    }
    else if (afrl::impact::isLineOfInterest(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::impact::LineOfInterest>(receivedLmcpMessage->m_object)->getLineID();
        m_linesOfInterest[id] = std::static_pointer_cast<afrl::impact::LineOfInterest>(receivedLmcpMessage->m_object);
    }
    else if (afrl::impact::isAreaOfInterest(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::impact::AreaOfInterest>(receivedLmcpMessage->m_object)->getAreaID();
        m_areasOfInterest[id] = std::static_pointer_cast<afrl::impact::AreaOfInterest>(receivedLmcpMessage->m_object);
    }
    else if (afrl::cmasi::isLoiterTask(receivedLmcpMessage->m_object.get()) ||
            afrl::cmasi::isMustFlyTask(receivedLmcpMessage->m_object.get()) ||
            afrl::cmasi::isAreaSearchTask(receivedLmcpMessage->m_object.get()) ||
            afrl::cmasi::isLineSearchTask(receivedLmcpMessage->m_object.get()) ||
            afrl::cmasi::isPointSearchTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isImpactPointSearchTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isImpactLineSearchTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isPatternSearchTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isAngledAreaSearchTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isCommRelayTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isWatchTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isBlockadeTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isCordonTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isEscortTask(receivedLmcpMessage->m_object.get()) ||
            afrl::impact::isMultiVehicleWatchTask(receivedLmcpMessage->m_object.get()))
    {
        auto task = std::static_pointer_cast<afrl::cmasi::Task>(receivedLmcpMessage->m_object);
        m_tasks[task->getTaskID()] = task;
        HandleTaskMsg(task);
    }
    return (false); // always false implies never terminating service from here
}

void BatchSummaryService::HandleTaskMsg(std::shared_ptr<afrl::cmasi::Task> task)
{
    m_taskLocations.erase(task->getTaskID());

    if (afrl::cmasi::isLoiterTask(task.get()))
    {
        std::shared_ptr<afrl::cmasi::LoiterTask> loiter(std::static_pointer_cast<afrl::cmasi::LoiterTask>(task));
        std::shared_ptr<afrl::cmasi::Location3D> loc(loiter->getDesiredAction()->getLocation()->clone());
        m_taskLocations[task->getTaskID()].push_back(loc);
        m_taskLengths[task->getTaskID()] = std::make_pair(loiter->getDesiredAction()->getDuration(), 0.0f);
    }
    else if (afrl::cmasi::isMustFlyTask(task.get()))
    {
        std::shared_ptr<afrl::cmasi::MustFlyTask> mustfly(std::static_pointer_cast<afrl::cmasi::MustFlyTask>(task));
        std::shared_ptr<afrl::cmasi::Location3D> loc(mustfly->getPosition()->clone());
        m_taskLocations[task->getTaskID()].push_back(loc);
        m_taskLengths[task->getTaskID()] = std::make_pair(0, 0.0f);
    }
    else if (afrl::impact::isCommRelayTask(task.get()))
    {
        auto commrelay = std::static_pointer_cast<afrl::impact::CommRelayTask>(task);
        int64_t towerId = commrelay->getTowerID();
        std::shared_ptr<afrl::cmasi::Location3D> towerLocation{nullptr};
        if (m_towerLocations.find(towerId) != m_towerLocations.end())
        {
            towerLocation = m_towerLocations[towerId];
        }

        // extract destination of supported entity
        std::shared_ptr<afrl::cmasi::Location3D> destinationLocation{nullptr};
        if (commrelay->getDestinationLocation())
        {
            destinationLocation.reset(commrelay->getDestinationLocation()->clone());
        }
        if (towerLocation && destinationLocation)
        {
            std::shared_ptr<afrl::cmasi::Location3D> targetLocation(new afrl::cmasi::Location3D);
            targetLocation->setLatitude((towerLocation->getLatitude() + destinationLocation->getLatitude()) / 2.0);
            targetLocation->setLongitude((towerLocation->getLongitude() + destinationLocation->getLongitude()) / 2.0);
            m_taskLocations[task->getTaskID()].push_back(targetLocation);
            m_taskLengths[task->getTaskID()] = std::make_pair(-1, 0.0f);
        }
    }
    else if (afrl::cmasi::isPointSearchTask(task.get()))
    {
        std::shared_ptr<afrl::cmasi::PointSearchTask> pointSearch(std::static_pointer_cast<afrl::cmasi::PointSearchTask>(task));
        std::shared_ptr<afrl::cmasi::Location3D> loc(pointSearch->getSearchLocation()->clone());
        m_taskLocations[task->getTaskID()].push_back(loc);
        m_taskLengths[task->getTaskID()] = std::make_pair(0, 0.0f);
    }
    else if (afrl::impact::isImpactPointSearchTask(task.get()))
    {
        std::shared_ptr<afrl::impact::ImpactPointSearchTask> pointSearch(std::static_pointer_cast<afrl::impact::ImpactPointSearchTask>(task));
        if (pointSearch->getSearchLocationID() == 0 &&
                pointSearch->getSearchLocation() != nullptr)
        {
            std::shared_ptr<afrl::cmasi::Location3D> loc(pointSearch->getSearchLocation()->clone());
            m_taskLocations[task->getTaskID()].push_back(loc);
            if (pointSearch->getDesiredAction())
            {
                m_taskLengths[task->getTaskID()] = std::make_pair(pointSearch->getDesiredAction()->getDuration(), 0.0f);
            }
            else
            {
                m_taskLengths[task->getTaskID()] = std::make_pair(1.0, 0.0f);
            }
        }
        else
        {
            // look up location from points of interest
            auto point = m_pointsOfInterest.find(pointSearch->getSearchLocationID());
            if (point != m_pointsOfInterest.end())
            {
                std::shared_ptr<afrl::cmasi::Location3D> loc(point->second->getLocation()->clone());
                m_taskLocations[task->getTaskID()].push_back(loc);
                if (pointSearch->getDesiredAction())
                {
                    m_taskLengths[task->getTaskID()] = std::make_pair(pointSearch->getDesiredAction()->getDuration(), 0.0f);
                }
                else
                {
                    m_taskLengths[task->getTaskID()] = std::make_pair(1.0, 0.0f);
                }
            }
        }
    }
    else if (afrl::impact::isPatternSearchTask(task.get()))
    {
        std::shared_ptr<afrl::impact::PatternSearchTask> patternSearch(std::static_pointer_cast<afrl::impact::PatternSearchTask>(task));
        if (patternSearch->getSearchLocationID() == 0 &&
                patternSearch->getSearchLocation() != nullptr)
        {
            std::shared_ptr<afrl::cmasi::Location3D> loc(patternSearch->getSearchLocation()->clone());
            m_taskLocations[task->getTaskID()].push_back(loc);
            m_taskLengths[task->getTaskID()] = std::make_pair(0, PatternLength(patternSearch));
        }
        else
        {
            // look up location from points of interest
            auto point = m_pointsOfInterest.find(patternSearch->getSearchLocationID());
            if (point != m_pointsOfInterest.end())
            {
                std::shared_ptr<afrl::cmasi::Location3D> loc(point->second->getLocation()->clone());
                m_taskLocations[task->getTaskID()].push_back(loc);
                m_taskLengths[task->getTaskID()] = std::make_pair(0, PatternLength(patternSearch));
            }
        }
    }
    else if (afrl::impact::isWatchTask(task.get()))
    {
        std::shared_ptr<afrl::impact::WatchTask> watchTask(std::static_pointer_cast<afrl::impact::WatchTask>(task));
        // look up current entity location
        auto entityLoc = m_entityStates.find(watchTask->getWatchedEntityID());
        if (entityLoc != m_entityStates.end())
        {
            std::shared_ptr<afrl::cmasi::Location3D> loc(entityLoc->second->getLocation()->clone());
            m_taskLocations[task->getTaskID()].push_back(loc);
            m_taskLengths[task->getTaskID()] = std::make_pair(-1, 0.0f);
        }
    }
    else if (afrl::cmasi::isLineSearchTask(task.get()))
    {
        std::shared_ptr<afrl::cmasi::LineSearchTask> lineSearch(std::static_pointer_cast<afrl::cmasi::LineSearchTask>(task));
        // add start and end of line
        if (!lineSearch->getPointList().empty())
        {
            std::shared_ptr<afrl::cmasi::Location3D> loc(lineSearch->getPointList().front()->clone());
            m_taskLocations[task->getTaskID()].push_back(loc);
            m_taskLengths[task->getTaskID()] = std::make_pair(0, LineSearchLength(lineSearch->getPointList()));
        }
        if (lineSearch->getPointList().size() > 1)
        {
            std::shared_ptr<afrl::cmasi::Location3D> loc(lineSearch->getPointList().back()->clone());
            m_taskLocations[task->getTaskID()].push_back(loc);
        }
    }
    else if (afrl::impact::isImpactLineSearchTask(task.get()))
    {
        std::shared_ptr<afrl::impact::ImpactLineSearchTask> lineSearch(std::static_pointer_cast<afrl::impact::ImpactLineSearchTask>(task));
        // look up line from lines of interest
        auto line = m_linesOfInterest.find(lineSearch->getLineID());
        if (line != m_linesOfInterest.end())
        {
            // add start and end of line
            if (!line->second->getLine().empty())
            {
                std::shared_ptr<afrl::cmasi::Location3D> loc(line->second->getLine().front()->clone());
                m_taskLocations[task->getTaskID()].push_back(loc);
                m_taskLengths[task->getTaskID()] = std::make_pair(0, LineSearchLength(line->second->getLine()));
            }
            if (line->second->getLine().size() > 1)
            {
                std::shared_ptr<afrl::cmasi::Location3D> loc(line->second->getLine().back()->clone());
                m_taskLocations[task->getTaskID()].push_back(loc);
            }
        }
    }
    else if (afrl::cmasi::isAreaSearchTask(task.get()))
    {
        std::shared_ptr<afrl::cmasi::AreaSearchTask> areaSearch(std::static_pointer_cast<afrl::cmasi::AreaSearchTask>(task));
        std::shared_ptr<afrl::cmasi::AbstractGeometry> geom(areaSearch->getSearchArea()->clone());
        AddPlanningPointsFromArea(task->getTaskID(), geom);
        m_taskLengths[task->getTaskID()] = std::make_pair(0, AreaSearchLength(geom));
    }
    else if (afrl::impact::isAngledAreaSearchTask(task.get()))
    {
        std::shared_ptr<afrl::impact::AngledAreaSearchTask> areaSearch(std::static_pointer_cast<afrl::impact::AngledAreaSearchTask>(task));
        auto area = m_areasOfInterest.find(areaSearch->getSearchAreaID());
        if (area != m_areasOfInterest.end())
        {
            std::shared_ptr<afrl::cmasi::AbstractGeometry> geom(area->second->getArea()->clone());
            AddPlanningPointsFromArea(task->getTaskID(), geom);
            m_taskLengths[task->getTaskID()] = std::make_pair(0, AreaSearchLength(geom));
        }
    }
    else if (afrl::impact::isBlockadeTask(task.get()))
    {
        auto blockTask = std::static_pointer_cast<afrl::impact::BlockadeTask>(task);
        if (blockTask->getNumberVehicles() > 1)
        {
            m_multiVehicleTasks.insert(task->getTaskID());
        }
        // look up current blocked entity location
        auto entityLoc = m_entityStates.find(blockTask->getBlockedEntityID());
        if (entityLoc != m_entityStates.end())
        {
            std::shared_ptr<afrl::cmasi::Location3D> loc(entityLoc->second->getLocation()->clone());
            m_taskLocations[task->getTaskID()].push_back(loc);
            m_taskLengths[task->getTaskID()] = std::make_pair(-1, 0.0f);
        }
    }
    else if (afrl::impact::isCordonTask(task.get()))
    {
        m_multiVehicleTasks.insert(task->getTaskID());
        auto cordonTask = std::static_pointer_cast<afrl::impact::CordonTask>(task);
        std::shared_ptr<afrl::cmasi::Location3D> loc(cordonTask->getCordonLocation()->clone());
        m_taskLocations[task->getTaskID()].push_back(loc);
        m_taskLengths[task->getTaskID()] = std::make_pair(-1, 0.0f);

        // build an 'egress route request' from the ground planner (external)
        auto egressRequest = std::shared_ptr<uxas::messages::route::EgressRouteRequest>(new uxas::messages::route::EgressRouteRequest);
        egressRequest->setStartLocation(cordonTask->getCordonLocation()->clone());
        egressRequest->setRadius(cordonTask->getStandoffDistance());

        // store and send request
        m_pendingEgressRequests.push_back(task->getTaskID());
        std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(egressRequest);
        sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::GroundPathPlanner(), pRequest);
    }
    else if (afrl::impact::isEscortTask(task.get()))
    {
        auto escortTask = std::static_pointer_cast<afrl::impact::EscortTask>(task);
        // look up current blocked entity location
        auto entityLoc = m_entityStates.find(escortTask->getSupportedEntityID());
        if (entityLoc != m_entityStates.end())
        {
            std::shared_ptr<afrl::cmasi::Location3D> loc(entityLoc->second->getLocation()->clone());
            m_taskLocations[task->getTaskID()].push_back(loc);
            m_taskLengths[task->getTaskID()] = std::make_pair(-1, 0.0f);
        }
    }
    else if (afrl::impact::isMultiVehicleWatchTask(task.get()))
    {
        auto nwatchTask = std::static_pointer_cast<afrl::impact::MultiVehicleWatchTask>(task);
        if (nwatchTask->getNumberVehicles() > 1)
        {
            m_multiVehicleTasks.insert(task->getTaskID());
        }
        // look up current blocked entity location
        auto entityLoc = m_entityStates.find(nwatchTask->getWatchedEntityID());
        if (entityLoc != m_entityStates.end())
        {
            std::shared_ptr<afrl::cmasi::Location3D> loc(entityLoc->second->getLocation()->clone());
            m_taskLocations[task->getTaskID()].push_back(loc);
            m_taskLengths[task->getTaskID()] = std::make_pair(-1, 0.0f);
        }
    }
}

void BatchSummaryService::HandleEgressRouteResponse(std::shared_ptr<uxas::messages::route::EgressRouteResponse> egress)
{
    // ASSUME: receive back in order sent, FUTURE: add request/response IDs
    if (!m_pendingEgressRequests.empty())
    {
        int64_t taskId = m_pendingEgressRequests.front();
        m_pendingEgressRequests.pop_front();
        m_egressPoints[taskId] = egress;

        // check all outstanding batch summary requests to see if this unlocks the continuation
        auto resp = m_readyResponse.begin();
        while (resp != m_readyResponse.end())
        {
            bool moveOn = true;
            if (m_workingResponse.find(*resp) != m_workingResponse.end())
            {
                for (auto t : m_workingResponse[*resp]->getSummaries())
                {
                    if (t->getTaskID() == taskId)
                    {
                        // candidate for re-evaluation
                        if (FinalizeBatchRequest(*resp))
                        {
                            moveOn = false;
                            break;
                        }
                    }
                }
            }
            if (moveOn)
            {
                ++resp;
            }
            else
            {
                resp = m_readyResponse.erase(resp);
            }
        }
    }
}

bool BatchSummaryService::FinalizeBatchRequest(int64_t responseId)
{
    // this function is only called when the summaries have been composed
    // only need to check for possible 'best efforts' regarding the tasks in the
    // current summary list

    if (m_workingResponse.find(responseId) == m_workingResponse.end())
        return false;
    auto resp = m_workingResponse[responseId];

    // check for cordon tasks in the summaries and build a complete task list
    for (auto s : resp->getSummaries())
    {
        int64_t taskId = s->getTaskID();
        if (m_tasks.find(taskId) != m_tasks.end())
        {
            if (afrl::impact::isCordonTask(m_tasks[taskId].get()))
            {
                if (m_egressPoints.find(taskId) == m_egressPoints.end())
                {
                    // not ready yet, wait for egress points to be received
                    return false;
                }
            }
        }
    }

    // at this point everything expected has been received, re-build summaries for multi-vehicle tasks
    auto cleanResp = std::shared_ptr<afrl::impact::BatchSummaryResponse>(new afrl::impact::BatchSummaryResponse);

    // add single vehicle task summaries and create list of multi-vehicle tasks to reason over
    std::unordered_map<int64_t, std::vector<std::shared_ptr<afrl::impact::VehicleSummary> > > summariesByTask;
    for (auto s : resp->getSummaries())
    {
        int64_t taskId = s->getTaskID();
        if (m_multiVehicleTasks.find(taskId) == m_multiVehicleTasks.end())
        {
            // copy over the summary if it's a single vehicle task
            cleanResp->getSummaries().push_back(s->clone());
        }
        else
        {
            // otherwise, add this task to the list of tasks to present as multi-vehicle
            for (auto v : s->getPerformingVehicles())
            {
                summariesByTask[taskId].push_back(std::shared_ptr<afrl::impact::VehicleSummary>(v->clone()));
            }
        }
    }

    // multi-vehicle tasks include [cordon, multi-overwatch, blockade] only
    for (auto t : summariesByTask)
    {
        if (m_tasks.find(t.first) != m_tasks.end())
        {
            if (afrl::impact::isCordonTask(m_tasks[t.first].get()))
            {
                // the egress points should exist here (checked earlier)
                if (m_egressPoints.find(t.first) != m_egressPoints.end())
                {
                    int64_t N = m_egressPoints[t.first]->getNodeLocations().size();
                    BuildSummaryOptions(t.first, cleanResp, t.second, N);
                }
            }
            else if (afrl::impact::isBlockadeTask(m_tasks[t.first].get()))
            {
                auto blockTask = std::static_pointer_cast<afrl::impact::BlockadeTask>(m_tasks[t.first]);
                int64_t N = blockTask->getNumberVehicles();
                BuildSummaryOptions(t.first, cleanResp, t.second, N);
            }
            else if (afrl::impact::isMultiVehicleWatchTask(m_tasks[t.first].get()))
            {
                auto multiWatchTask = std::static_pointer_cast<afrl::impact::MultiVehicleWatchTask>(m_tasks[t.first]);
                int64_t N = multiWatchTask->getNumberVehicles();
                BuildSummaryOptions(t.first, cleanResp, t.second, N);
            }
            else // somehow it is a multi-vehicle task but of unknown type
            {
                // just add all the summaries and call it good
                auto tsum = new afrl::impact::TaskSummary;
                tsum->setTaskID(t.first);
                for (auto v : t.second)
                {
                    tsum->getPerformingVehicles().push_back(v->clone());
                }
            }
        }
        else
        {
            // just add all the summaries and call it good
            auto tsum = new afrl::impact::TaskSummary;
            tsum->setTaskID(t.first);
            for (auto v : t.second)
            {
                tsum->getPerformingVehicles().push_back(v->clone());
            }
        }
    }

    if (!cleanResp->getSummaries().empty())
    {
        // Finally re-constructed an full batch response, send along to global
        std::shared_ptr<avtas::lmcp::Object> pResponse = std::static_pointer_cast<avtas::lmcp::Object>(cleanResp);
        sendSharedLmcpObjectBroadcastMessage(pResponse);
    }

    // clear out this working response from the map
    m_workingResponse.erase(responseId);

    return true;
}

void BatchSummaryService::BuildSummaryOptions(int64_t taskId, std::shared_ptr<afrl::impact::BatchSummaryResponse>& response,
        std::vector<std::shared_ptr<afrl::impact::VehicleSummary> >& vehicles, int64_t N)
{
    auto scratchResponse = std::shared_ptr<afrl::impact::BatchSummaryResponse>(new afrl::impact::BatchSummaryResponse);
    // 100% completion is achieved by having N vehicles on task
    int64_t K = vehicles.size();
    int64_t startN = K - 1; // start with max number of vehicles
    if (startN >= N) // or max number of points
    { // if starting at n=0, then all combinations from 1 .. K
        startN = N - 1;
    }
    for (int64_t n = startN; n < N && n < K; n++)
    {
        auto tsum = new afrl::impact::TaskSummary;
        tsum->setTaskID(taskId);
        tsum->setBestEffort((n + 1.0) / N);
        std::vector<int> v(K);
        std::iota(v.begin(), v.end(), 0);
        for_each_permutation<std::vector<int>::iterator, f>(v.begin(), v.begin() + (n + 1), v.end(), f(tsum, vehicles, scratchResponse));
        delete tsum;
    }

    std::vector< std::tuple<int64_t, size_t, std::unordered_set<int64_t> > > combinations;
    for (size_t r = 0; r < scratchResponse->getSummaries().size(); r++)
    {
        std::unordered_set<int64_t> scratch;
        int64_t sumTime = 0;
        for (auto v : scratchResponse->getSummaries().at(r)->getPerformingVehicles())
        {
            scratch.insert(v->getVehicleID());
            sumTime += v->getTimeToArrive();
        }

        bool isInCombinations = false;
        for (auto c : combinations)
        {
            bool isEquivalent = true;
            for (auto e : scratch)
            {
                if (std::get<2>(c).find(e) == std::get<2>(c).end())
                {
                    isEquivalent = false;
                    break;
                }
            }

            if (isEquivalent)
            {
                isInCombinations = true;
                // check update index/time
                if (sumTime < std::get<0>(c))
                {
                    std::get<0>(c) = sumTime;
                    std::get<1>(c) = r;
                }
                break;
            }
        }

        if (!isInCombinations)
        {
            combinations.push_back(std::make_tuple(sumTime, r, scratch));
        }
    }

    for (auto c : combinations)
    {
        response->getSummaries().push_back(scratchResponse->getSummaries().at(std::get<1>(c))->clone());
    }
}

float BatchSummaryService::PatternLength(std::shared_ptr<afrl::impact::PatternSearchTask> patternSearch)
{
    // estimated from lane spacing parameter
    double R = patternSearch->getExtent();
    double l = 2.0 * n_Const::c_Convert::dPi() * R*R;
    if (m_laneSpacing > 1.0)
    {
        l /= m_laneSpacing;
    }
    return l;
}

float BatchSummaryService::LineSearchLength(std::vector<afrl::cmasi::Location3D*>& line)
{
    if (line.empty())
        return 0.0f;

    uxas::common::utilities::CUnitConversions flatEarth;
    double north, east;
    flatEarth.ConvertLatLong_degToNorthEast_m(line.at(0)->getLatitude(), line.at(0)->getLongitude(), north, east);

    double length = 0.0;
    for (size_t k = 1; k < line.size(); k++)
    {
        double north_next, east_next;
        flatEarth.ConvertLatLong_degToNorthEast_m(line.at(k)->getLatitude(), line.at(k)->getLongitude(), north_next, east_next);
        length += sqrt((east - east_next)*(east - east_next) + (north - north_next)*(north - north_next));
        north = north_next;
        east = east_next;
    }
    return length;
}

float BatchSummaryService::AreaSearchLength(std::shared_ptr<afrl::cmasi::AbstractGeometry> geom)
{
    // estimated from lane spacing parameter
    uxas::common::utilities::CUnitConversions flatEarth;
    double w = 0.0;
    double h = 0.0;

    if (afrl::cmasi::isPolygon(geom.get()))
    {
        std::shared_ptr<afrl::cmasi::Polygon> polyLatLon = std::static_pointer_cast<afrl::cmasi::Polygon>(geom);

        // build euclidean polygon from lat/lon description
        std::vector< VisiLibity::Point > polygonVertices;
        for (size_t n = 0; n < polyLatLon->getBoundaryPoints().size(); n++)
        {
            double north, east;
            flatEarth.ConvertLatLong_degToNorthEast_m(polyLatLon->getBoundaryPoints().at(n)->getLatitude(), polyLatLon->getBoundaryPoints().at(n)->getLongitude(), north, east);
            polygonVertices.push_back(VisiLibity::Point(east, north));
        }
        VisiLibity::Polygon poly(polygonVertices);

        // remove excess points
        poly.eliminate_redundant_vertices(1.0);
        w = fabs(poly.bbox().x_max - poly.bbox().x_min);
        h = fabs(poly.bbox().y_max - poly.bbox().y_min);

    }
    else if (afrl::cmasi::isCircle(geom.get()))
    {
        std::shared_ptr<afrl::cmasi::Circle> circle = std::static_pointer_cast<afrl::cmasi::Circle>(geom);
        double r = circle->getRadius();
        w = 2 * r;
        h = 2 * r;
    }
    else if (afrl::cmasi::isRectangle(geom.get()))
    {
        std::shared_ptr<afrl::cmasi::Rectangle> rect = std::static_pointer_cast<afrl::cmasi::Rectangle>(geom);
        w = rect->getWidth();
        h = rect->getHeight();
    }

    double area = w*h;
    if (m_laneSpacing > 1.0)
    {
        area /= m_laneSpacing;
    }

    return area;
}

void BatchSummaryService::AddPlanningPointsFromArea(int64_t taskId, std::shared_ptr<afrl::cmasi::AbstractGeometry> geom)
{
    uxas::common::utilities::CUnitConversions flatEarth;

    if (afrl::cmasi::isPolygon(geom.get()))
    {
        std::shared_ptr<afrl::cmasi::Polygon> polyLatLon = std::static_pointer_cast<afrl::cmasi::Polygon>(geom);

        // build euclidean polygon from lat/lon description
        std::vector< VisiLibity::Point > polygonVertices;
        for (size_t n = 0; n < polyLatLon->getBoundaryPoints().size(); n++)
        {
            double north, east;
            flatEarth.ConvertLatLong_degToNorthEast_m(polyLatLon->getBoundaryPoints().at(n)->getLatitude(), polyLatLon->getBoundaryPoints().at(n)->getLongitude(), north, east);
            polygonVertices.push_back(VisiLibity::Point(east, north));
        }
        VisiLibity::Polygon poly(polygonVertices);

        // remove excess points
        poly.eliminate_redundant_vertices(1.0);

        // find centroid of polygon
        VisiLibity::Point c = poly.centroid();

        // sort the vertices by distance from centroid
        std::map<double, VisiLibity::Point> sortedDistance;
        for (size_t n = 0; n < polygonVertices.size(); n++)
        {
            double dist = VisiLibity::distance(c, polygonVertices.at(n));
            sortedDistance[dist] = polygonVertices.at(n);
        }

        // add furthest 4 points to planning list
        size_t iter = 0;
        for (auto i = sortedDistance.rbegin(); i != sortedDistance.rend() && iter < 4; i++)
        {
            double lat, lon;
            flatEarth.ConvertNorthEast_mToLatLong_deg(i->second.y(), i->second.x(), lat, lon);
            std::shared_ptr<afrl::cmasi::Location3D> loc(new afrl::cmasi::Location3D());
            loc->setLatitude(lat);
            loc->setLongitude(lon);
            m_taskLocations[taskId].push_back(loc);
            iter++;
        }
    }
    else if (afrl::cmasi::isCircle(geom.get()))
    {
        std::shared_ptr<afrl::cmasi::Circle> circle = std::static_pointer_cast<afrl::cmasi::Circle>(geom);
        double north, east;
        flatEarth.ConvertLatLong_degToNorthEast_m(circle->getCenterPoint()->getLatitude(), circle->getCenterPoint()->getLongitude(), north, east);
        double r = circle->getRadius();

        std::vector< VisiLibity::Point > corners;
        corners.push_back(VisiLibity::Point(east + r, north + r));
        corners.push_back(VisiLibity::Point(east - r, north + r));
        corners.push_back(VisiLibity::Point(east - r, north - r));
        corners.push_back(VisiLibity::Point(east + r, north - r));

        AddCorners(taskId, corners);
    }
    else if (afrl::cmasi::isRectangle(geom.get()))
    {
        std::shared_ptr<afrl::cmasi::Rectangle> rect = std::static_pointer_cast<afrl::cmasi::Rectangle>(geom);
        double north, east;
        flatEarth.ConvertLatLong_degToNorthEast_m(rect->getCenterPoint()->getLatitude(), rect->getCenterPoint()->getLongitude(), north, east);
        double w = rect->getWidth();
        double h = rect->getHeight();
        // note: north-aligned positive rotation is opposite direction of x-aligned positive rotation
        double a = -rect->getRotation() * n_Const::c_Convert::dDegreesToRadians();

        VisiLibity::Point c(east, north);
        std::vector< VisiLibity::Point > corners;
        corners.push_back(VisiLibity::Point(east + w, north + h).rotate(c, a));
        corners.push_back(VisiLibity::Point(east - w, north + h).rotate(c, a));
        corners.push_back(VisiLibity::Point(east - w, north - h).rotate(c, a));
        corners.push_back(VisiLibity::Point(east + w, north - h).rotate(c, a));

        AddCorners(taskId, corners);
    }
}

void BatchSummaryService::AddCorners(int64_t taskId, std::vector<VisiLibity::Point>& corners)
{
    // add north/east defined points to candidate planning location list after conversion to lat/lon
    uxas::common::utilities::CUnitConversions flatEarth;
    for (size_t n = 0; n < corners.size(); n++)
    {
        double lat, lon;
        flatEarth.ConvertNorthEast_mToLatLong_deg(corners.at(n).y(), corners.at(n).x(), lat, lon);
        std::shared_ptr<afrl::cmasi::Location3D> loc(new afrl::cmasi::Location3D());
        loc->setLatitude(lat);
        loc->setLongitude(lon);
        m_taskLocations[taskId].push_back(loc);
    }
}

void BatchSummaryService::HandleBatchSummaryRequest(std::shared_ptr<afrl::impact::BatchSummaryRequest> request)
{
    //// ignore duplicate requests
    //if (request->operator==(*m_workingRequest))
    //    return;
    //
    //if (m_workingRequest)
    //    delete m_workingRequest;
    //m_workingRequest = request->clone();

    int64_t responseId = m_responseId;
    m_responseId++;
    m_workingResponse[responseId].reset(new afrl::impact::BatchSummaryResponse);

    std::vector< std::shared_ptr<uxas::messages::route::RoutePlanRequest> > sendLocal;
    std::vector< std::shared_ptr<uxas::messages::route::RoutePlanRequest> > sendGlobal;

    // make a separate request for each vehicle
    for (size_t v = 0; v < request->getVehicles().size(); v++)
    {
        int64_t vehicleId = request->getVehicles().at(v);

        // only check vehicles that have valid states
        auto vehicle = m_entityStates.find(vehicleId);
        if (vehicle != m_entityStates.end())
        {
            // request a plan for each task point
            for (size_t t = 0; t < request->getTaskList().size(); t++)
            {
                int64_t taskId = request->getTaskList().at(t);

                auto taskPts = m_taskLocations.find(taskId);
                if (taskPts != m_taskLocations.end() && !taskPts->second.empty())
                {
                    // create a new route plan request
                    std::shared_ptr<uxas::messages::route::RoutePlanRequest> planRequest(new uxas::messages::route::RoutePlanRequest);
                    planRequest->setAssociatedTaskID(taskId);
                    planRequest->setIsCostOnlyRequest(false); // need full path for out-of-comm calculation
                    planRequest->setOperatingRegion(request->getOperatingRegion());
                    planRequest->setVehicleID(vehicleId);

                    // request routes from initial conditions
                    for (size_t p = 0; p < taskPts->second.size(); p++)
                    {
                        std::shared_ptr<afrl::cmasi::Location3D> loc = taskPts->second.at(p);
                        uxas::messages::route::RouteConstraints* r = new uxas::messages::route::RouteConstraints;
                        r->setStartLocation(vehicle->second->getLocation()->clone());
                        r->setEndLocation(loc->clone());
                        r->setRouteID(m_routeId);
                        planRequest->getRouteRequests().push_back(r);
                        m_pendingRouteResponses[m_routeId] = responseId;
                        m_routeTaskPairing[m_routeId] = std::make_tuple(vehicleId, taskId, 0);
                        m_routeId++;
                    }

                    // send this plan request to an off-board route planner for ground vehicles
                    if (m_groundVehicles.find(vehicleId) != m_groundVehicles.end())
                    {
                        sendGlobal.push_back(planRequest);
                    }
                    else
                    {
                        sendLocal.push_back(planRequest);
                    }
                }
            }
        }
    }

    // send locally all plans
    for (size_t k = 0; k < sendLocal.size(); k++)
    {
        std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(sendLocal.at(k));
        sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::AircraftPathPlanner(), pRequest);
    }

    // send globally all plans
    for (size_t k = 0; k < sendGlobal.size(); k++)
    {
        std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(sendGlobal.at(k));
        if (m_fastPlan)
        {
            EuclideanPlan(sendGlobal.at(k));
        }
        else
        {
            // send to ground planner
            sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::GroundPathPlanner(), pRequest);
        }
    }
}

void BatchSummaryService::EuclideanPlan(std::shared_ptr<uxas::messages::route::RoutePlanRequest> request)
{
    uxas::common::utilities::CUnitConversions flatEarth;
    int64_t regionId = request->getOperatingRegion();
    int64_t vehicleId = request->getVehicleID();
    int64_t taskId = request->getAssociatedTaskID();
    std::shared_ptr<uxas::messages::route::RoutePlanResponse> response(new uxas::messages::route::RoutePlanResponse);
    response->setAssociatedTaskID(taskId);
    response->setVehicleID(vehicleId);
    response->setOperatingRegion(regionId);

    for (size_t k = 0; k < request->getRouteRequests().size(); k++)
    {
        uxas::messages::route::RouteConstraints* routeRequest = request->getRouteRequests().at(k);
        int64_t routeId = routeRequest->getRouteID();
        VisiLibity::Point startPt, endPt;
        double north, east;

        uxas::messages::route::RoutePlan* plan = new uxas::messages::route::RoutePlan;
        plan->setRouteID(routeId);

        flatEarth.ConvertLatLong_degToNorthEast_m(routeRequest->getStartLocation()->getLatitude(), routeRequest->getStartLocation()->getLongitude(), north, east);
        startPt.set_x(east);
        startPt.set_y(north);

        flatEarth.ConvertLatLong_degToNorthEast_m(routeRequest->getEndLocation()->getLatitude(), routeRequest->getEndLocation()->getLongitude(), north, east);
        endPt.set_x(east);
        endPt.set_y(north);

        double linedist = VisiLibity::distance(startPt, endPt);
        if (m_entityConfigs.find(vehicleId) != m_entityConfigs.end())
        {
            if (m_entityConfigs[vehicleId]->getNominalSpeed() > 0.1)
            {
                linedist /= m_entityConfigs[vehicleId]->getNominalSpeed();
            }
        }
        plan->setRouteCost(linedist);

        response->getRouteResponses().push_back(plan);
    }
    HandleRoutePlanResponse(response);
}

void BatchSummaryService::UpdateSummary(afrl::impact::VehicleSummary* sum, uxas::messages::route::RoutePlan * plan)
{
    // extract speed from configuration
    double speed = 1.0;
    if (m_entityConfigs.find(sum->getVehicleID()) != m_entityConfigs.end())
    {
        speed = m_entityConfigs[sum->getVehicleID()]->getNominalSpeed();
        if (speed < 1.0)
            speed = 1.0;
    }

    // set time to arrive from route planner
    sum->setTimeToArrive(plan->getRouteCost() * 1000);

    // Look up task timing
    if (m_taskLengths.find(sum->getDestinationTaskID()) != m_taskLengths.end())
    {
        if (m_taskLengths[sum->getDestinationTaskID()].second > 1e-4)
        {
            sum->setTimeOnTask(m_taskLengths[sum->getDestinationTaskID()].second / speed * 1000);
        }
        else
        {
            sum->setTimeOnTask(m_taskLengths[sum->getDestinationTaskID()].first);
        }
    }

    // calculate 'EnergyRemaining'
    sum->setEnergyRemaining(100.0f);

    if (m_entityStates.find(sum->getVehicleID()) != m_entityStates.end())
    {
        // get current energy of vehicle and energy expenditure rate
        double e = m_entityStates[sum->getVehicleID()]->getEnergyAvailable(); // %
        double erate = m_entityStates[sum->getVehicleID()]->getActualEnergyRate(); // %/s

        // use time to go and time on task to get full time
        int64_t time = sum->getTimeToArrive();
        if (sum->getTimeOnTask() > 0)
        {
            time += sum->getTimeOnTask();
        }

        // linear approximation of energy remaining
        double eloss = time * erate / 1000.0; // time back to seconds from milliseconds
        e -= eloss;
        e = (e < 0) ? 0.0 : e;
        sum->setEnergyRemaining(e);
    }

    // check comm range
    bool inCommRange = false;
    for (auto t : m_towerLocations)
    {
        bool beyondThisTower = false;
        uxas::common::utilities::CUnitConversions flatEarth;
        double tn, te;
        flatEarth.ConvertLatLong_degToNorthEast_m(t.second->getLatitude(), t.second->getLongitude(), tn, te);

        if (m_entityStates.find(sum->getVehicleID()) != m_entityStates.end() &&
                m_towerRanges.find(t.first) != m_towerRanges.end())
        {
            double vn, ve;
            double towerRange = m_towerRanges[t.first].first;
            if (!m_towerRanges[t.first].second)
            {
                towerRange = 1.0;
            }

            // set to max of vehicle, tower
            if (m_entityConfigs.find(sum->getVehicleID()) != m_entityConfigs.end())
            {
                for (auto pay : m_entityConfigs[sum->getVehicleID()]->getPayloadConfigurationList())
                {
                    if (afrl::impact::isRadioConfiguration(pay))
                    {
                        auto commpay = static_cast<afrl::impact::RadioConfiguration*> (pay);
                        if (commpay->getRange() > towerRange)
                        {
                            towerRange = commpay->getRange();
                        }
                    }
                }
            }

            flatEarth.ConvertLatLong_degToNorthEast_m(
                    m_entityStates[sum->getVehicleID()]->getLocation()->getLatitude(),
                    m_entityStates[sum->getVehicleID()]->getLocation()->getLongitude(), vn, ve);
            double vdist = sqrt((tn - vn)*(tn - vn) + (te - ve)*(te - ve));
            beyondThisTower = (vdist > towerRange);

            for (auto p : plan->getWaypoints())
            {
                if (beyondThisTower)
                    break;
                double pn, pe;
                flatEarth.ConvertLatLong_degToNorthEast_m(p->getLatitude(), p->getLongitude(), pn, pe);
                double pdist = sqrt((tn - pn)*(tn - pn) + (te - pe)*(te - pe));
                for (auto a : p->getVehicleActionList())
                {
                    if (afrl::cmasi::isLoiterAction(a))
                    {
                        auto la = static_cast<afrl::cmasi::LoiterAction*> (a);
                        double wn, we;
                        flatEarth.ConvertLatLong_degToNorthEast_m(
                                la->getLocation()->getLatitude(),
                                la->getLocation()->getLongitude(), wn, we);
                        double wpdist = sqrt((wn - tn)*(wn - tn) + (we - te)*(we - te));
                        if ((la->getRadius() + wpdist) > pdist)
                        {
                            // override distance if action is futher than waypoint
                            pdist = la->getRadius() + wpdist;
                        }
                    }
                }
                beyondThisTower |= (pdist > towerRange);
            }
        }
        if (!beyondThisTower)
        {
            inCommRange = true;
            break;
        }
    }

    sum->setBeyondCommRange(!inCommRange);
}

void BatchSummaryService::HandleRoutePlanResponse(std::shared_ptr<uxas::messages::route::RoutePlanResponse> response)
{
    // make sure I get everything back that I requested
    for (size_t i = 0; i < response->getRouteResponses().size(); i++)
    {
        uxas::messages::route::RoutePlan* plan = response->getRouteResponses().at(i);
        auto pairing = m_routeTaskPairing.find(plan->getRouteID());
        if (pairing != m_routeTaskPairing.end())
        {
            int64_t vehicleId = std::get<0>(pairing->second);
            int64_t taskId = std::get<1>(pairing->second);
            int64_t prevTaskId = std::get<2>(pairing->second);

            int64_t responseId = 0;
            if (m_pendingRouteResponses.find(plan->getRouteID()) != m_pendingRouteResponses.end())
            {
                responseId = m_pendingRouteResponses[plan->getRouteID()];
            }

            if (m_workingResponse.find(responseId) != m_workingResponse.end())
            {
                bool hasSummary = false;
                for (size_t k = 0; k < m_workingResponse[responseId]->getSummaries().size(); k++)
                {
                    afrl::impact::TaskSummary* tsum = m_workingResponse[responseId]->getSummaries().at(k);
                    if (tsum->getTaskID() == taskId)
                    {
                        for (auto& sum : tsum->getPerformingVehicles())
                        {
                            if (sum->getVehicleID() == vehicleId &&
                                    sum->getDestinationTaskID() == taskId)
                            {
                                if (plan->getRouteCost() >= 0.0)
                                {
                                    // put lowest time to go as cost (convert from seconds to milliseconds)
                                    // so of all options available to start the task, this one will return lowest feasible cost
                                    if (sum->getTimeToArrive() < 0 || sum->getTimeToArrive() < plan->getRouteCost() * 1000)
                                    {
                                        UpdateSummary(sum, plan);
                                    }
                                }
                                hasSummary = true;
                                break;
                            }
                        }
                    }
                }

                // no exisiting summary, so add one
                if (!hasSummary)
                {
                    afrl::impact::TaskSummary* tsum = new afrl::impact::TaskSummary;
                    tsum->setTaskID(taskId);
                    afrl::impact::VehicleSummary* sum = new afrl::impact::VehicleSummary;
                    sum->setVehicleID(vehicleId);
                    sum->setDestinationTaskID(taskId);
                    sum->setTimeToArrive(-1);
                    if (plan->getRouteCost() >= 0.0)
                    {
                        UpdateSummary(sum, plan);
                    }
                    tsum->getPerformingVehicles().push_back(sum);
                    m_workingResponse[responseId]->getSummaries().push_back(tsum);
                }
            }
        }

        // should be properly processed
        m_pendingRouteResponses.erase(plan->getRouteID());
    }

    // if there is nothing left pending and there are summaries to send, do so
    for (auto i : m_workingResponse)
    {
        bool isPending = false;
        for (auto j = m_pendingRouteResponses.begin(); j != m_pendingRouteResponses.end(); j++)
        {
            // check to see if a route id that is pending matches the response id to be sent
            if (j->second == i.first)
            {
                isPending = true;
                break;
            }
        }

        // if there are no more pending routes for this response, then send it
        if (!isPending)
        {
            // add it to the 'ready' list
            m_readyResponse.insert(i.first);
        }
    }

    auto fr = m_readyResponse.begin();
    while (fr != m_readyResponse.end())
    {
        // attempt to send all those that are ready
        if (FinalizeBatchRequest(*fr))
        {
            fr = m_readyResponse.erase(fr);
        }
        else
        {
            ++fr;
        }
    }
}

}; //namespace service
}; //namespace uxas

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_RouteAggregator.cpp
 * Author: derek
 * 
 * Created on Aug 2, 2015, 8:21 AM
 */

#include "RouteAggregatorService.h"

#include "UxAS_Log.h"
#include "pugixml.hpp"
#include "UnitConversions.h"
#include "DRand.h"
#include "Constants/UxAS_String.h"

#include <map>

#define STRING_COMPONENT_NAME "RouteAggregator"
#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME
#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_FAST_PLAN "FastPlan"

namespace uxas
{
namespace service
{
RouteAggregatorService::ServiceBase::CreationRegistrar<RouteAggregatorService>
RouteAggregatorService::s_registrar(RouteAggregatorService::s_registryServiceTypeNames());

RouteAggregatorService::RouteAggregatorService()
: ServiceBase(RouteAggregatorService::s_typeName(), RouteAggregatorService::s_directoryName()) { };

RouteAggregatorService::~RouteAggregatorService() { };

bool
RouteAggregatorService::initialize()
{
    return true;
}

bool
RouteAggregatorService::configure(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();

    if (!ndComponent.attribute(STRING_XML_FAST_PLAN).empty())
    {
        // Only supported parameter: disables local route planner for
        // computationally expensive ground route calculations
        m_fastPlan = ndComponent.attribute(STRING_XML_FAST_PLAN).as_bool();
    }

    // track states and configurations for assignment cost matrix calculation
    // [EntityStates] are used to calculate costs from current position to first task
    // [EntityConfigurations] are used for nominal speed values (all costs are in terms of time to arrive)
    
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

    // track requests to kickoff matrix calculation
    addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);

    // subscribe to task plan options to build matrix
    addSubscriptionAddress(uxas::messages::task::TaskPlanOptions::Subscription);

    // handle batch route requests
    addSubscriptionAddress(uxas::messages::route::RouteRequest::Subscription);

    // listen for responses to requests from route planner(s)
    addSubscriptionAddress(uxas::messages::route::RoutePlanResponse::Subscription);

    // Subscribe to group messages (whisper from local route planner)
    //TODO REVIEW DESIGN "RouteAggregator" "RoutePlanner" flip message addressing effecting session behavior


    return true; // may not have the proper fast plan value, but proceed anyway
}

bool
RouteAggregatorService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    // successful de-serialization of message
    if (uxas::messages::route::isRoutePlanResponse(receivedLmcpMessage->m_object.get()))
    {
        auto rplan = std::static_pointer_cast<uxas::messages::route::RoutePlanResponse>(receivedLmcpMessage->m_object);
        m_routePlanResponses[rplan->getResponseID()] = rplan;
        for (auto p : rplan->getRouteResponses())
        {
            m_routePlans[p->getRouteID()] = std::make_pair(rplan->getResponseID(), std::shared_ptr<uxas::messages::route::RoutePlan>(p->clone()));
        }
        CheckAllRoutePlans();
    }
    else if (uxas::messages::route::isRouteRequest(receivedLmcpMessage->m_object.get()))
    {
        auto rreq = std::static_pointer_cast<uxas::messages::route::RouteRequest>(receivedLmcpMessage->m_object);
        HandleRouteRequest(rreq);
    }
    else if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpMessage->m_object))
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
    else if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(receivedLmcpMessage->m_object))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
        m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        m_airVehicles.insert(id);
    }
    else if (afrl::vehicles::isGroundVehicleConfiguration(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
        m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        m_groundVehicles.insert(id);
    }
    else if (afrl::vehicles::isSurfaceVehicleConfiguration(receivedLmcpMessage->m_object.get()))
    {
        int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
        m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        m_surfaceVehicles.insert(id);
    }
    else if (uxas::messages::task::isUniqueAutomationRequest(receivedLmcpMessage->m_object.get()))
    {
        auto areq = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage->m_object);
        m_uniqueAutomationRequests[m_autoRequestId++] = areq;
        //ResetTaskOptions(areq); // clear m_taskOptions and wait for refresh from tasks
        CheckAllTaskOptionsReceived();
    }
    else if (afrl::impact::isImpactAutomationRequest(receivedLmcpMessage->m_object.get()))
    {
        auto sreq = std::static_pointer_cast<afrl::impact::ImpactAutomationRequest>(receivedLmcpMessage->m_object);
        auto areq = std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>();
        areq->setOriginalRequest(sreq->getTrialRequest()->clone());
        m_uniqueAutomationRequests[m_autoRequestId++] = areq;
        areq->setRequestID(m_autoRequestId);
        //ResetTaskOptions(areq); // clear m_taskOptions and wait for refresh from tasks
        CheckAllTaskOptionsReceived();
    }
    else if (uxas::messages::task::isTaskPlanOptions(receivedLmcpMessage->m_object.get()))
    {
        auto taskOptions = std::static_pointer_cast<uxas::messages::task::TaskPlanOptions>(receivedLmcpMessage->m_object);
        m_taskOptions[taskOptions->getTaskID()] = taskOptions;
        CheckAllTaskOptionsReceived();
    }
    return (false); // always false implies never terminating service from here
}

void RouteAggregatorService::CheckAllTaskOptionsReceived()
{
    // loop through all automation requests; delete when fulfilled
    auto areqIter = m_uniqueAutomationRequests.begin();
    while (areqIter != m_uniqueAutomationRequests.end())
    {
        // check that to see if all options from all tasks have been received for this request
        bool isAllReceived{true};
        for (size_t t = 0; t < areqIter->second->getOriginalRequest()->getTaskList().size(); t++)
        {
            int64_t taskId = areqIter->second->getOriginalRequest()->getTaskList().at(t);
            if (m_taskOptions.find(taskId) == m_taskOptions.end())
            {
                isAllReceived = false;
                break;
            }
        }

        // if all task options have NOT been received, wait until more come
        if (isAllReceived)
        {
            // Build messages for matrix
            BuildMatrixRequests(areqIter->first, areqIter->second);

        }
        areqIter++;
    }
}

void RouteAggregatorService::BuildMatrixRequests(int64_t reqId, const std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>& areq)
{
    // All options corresponding to current automation request have been received
    // now make 'matrix' requests (all task options to all other task options)
    // [but only if options haven't already been sent??]

    // Proceedure:
    //  1. Create new 'pending' data structure for all routes that will fulfill this request
    //  2. For each vehicle, create requests for:
    //       a. initial position to each task option
    //       b. task/option to task/option
    //       c. associate routeID with task options in m_routeTaskPairing
    //       d. push routeID onto pending list
    //  3. Send requests to proper planners

    m_pendingAutoReq[reqId] = std::unordered_set<int64_t>();
    std::vector< std::shared_ptr<uxas::messages::route::RoutePlanRequest> > sendAirPlanRequest;
    std::vector< std::shared_ptr<uxas::messages::route::RoutePlanRequest> > sendGroundPlanRequest;
    
    // if the 'EntityList' is empty, then ALL vehicles are considered eligible
    if(areq->getOriginalRequest()->getEntityList().empty())
    {
        for(auto entity : m_entityStates)
        {
            areq->getOriginalRequest()->getEntityList().push_back(entity.second->getID());
        }
    }

    // to minimize network traffic make a separate request for each vehicle
    for (size_t v = 0; v < areq->getOriginalRequest()->getEntityList().size(); v++)
    {
        // only check vehicles that have valid states
        int64_t vehicleId = areq->getOriginalRequest()->getEntityList().at(v);
        auto vehicle = m_entityStates.find(vehicleId);

        float startHeading_deg{0.0};
        auto startLocation = std::shared_ptr<afrl::cmasi::Location3D>();
        bool isFoundPlannningState{false};
        for (auto& planningState : areq->getPlanningStates())
        {
            if (planningState->getEntityID() == vehicleId)
            {
                startLocation.reset(planningState->getPlanningPosition()->clone());
                startHeading_deg = planningState->getPlanningHeading();
                isFoundPlannningState = true;
                break;
            }
        }

        if (isFoundPlannningState || (vehicle != m_entityStates.end()))
        {
            // build list of eligible task options
            std::vector<std::shared_ptr<uxas::messages::task::TaskOption> > taskOptionList;
            for (size_t t = 0; t < areq->getOriginalRequest()->getTaskList().size(); t++)
            {
                int64_t taskId = areq->getOriginalRequest()->getTaskList().at(t);
                if (m_taskOptions.find(taskId) != m_taskOptions.end())
                {
                    for (size_t o = 0; o < m_taskOptions[taskId]->getOptions().size(); o++)
                    {
                        auto option = m_taskOptions[taskId]->getOptions().at(o);

                        auto elig = std::find_if(option->getEligibleEntities().begin(), option->getEligibleEntities().end(),
                                                 [&](int64_t v)
                                                 {
                                                     return v == vehicleId; });
                        if (option->getEligibleEntities().empty() || elig != option->getEligibleEntities().end())
                        {
                            taskOptionList.push_back(std::shared_ptr<uxas::messages::task::TaskOption>(option->clone()));
                        }
                    }
                }
            }

            // create a new route plan request
            std::shared_ptr<uxas::messages::route::RoutePlanRequest> planRequest(new uxas::messages::route::RoutePlanRequest);
            planRequest->setAssociatedTaskID(0); // mapping from routeID to proper task
            planRequest->setIsCostOnlyRequest(false);  // request full path for more accurate timing information
            planRequest->setOperatingRegion(areq->getOriginalRequest()->getOperatingRegion());
            planRequest->setVehicleID(vehicleId);
            //planRequest->setRouteID(m_planrequestId);
            //m_planrequestId++;

            if (!isFoundPlannningState)
            {
                assert(vehicle != m_entityStates.end());
                startLocation.reset(vehicle->second->getLocation()->clone());
                startHeading_deg = vehicle->second->getHeading();
            }

            // find routes from initial conditions
            for (size_t t = 0; t < taskOptionList.size(); t++)
            {
                auto option = taskOptionList.at(t);

                // build map from request to full task/option information
                AggregatorTaskOptionPair* top = new AggregatorTaskOptionPair(vehicleId, 0, 0, option->getTaskID(), option->getOptionID());
                m_routeTaskPairing[m_routeId] = std::shared_ptr<AggregatorTaskOptionPair>(top);

                uxas::messages::route::RouteConstraints* r = new uxas::messages::route::RouteConstraints;
                r->setStartLocation(startLocation->clone());
                r->setStartHeading(startHeading_deg);
                r->setEndLocation(option->getStartLocation()->clone());
                r->setEndHeading(option->getStartHeading());
                r->setRouteID(m_routeId);
                planRequest->getRouteRequests().push_back(r);
                m_pendingAutoReq[reqId].insert(m_routeId);
                m_routeId++;
            }

            // found routes between all task options
            for (size_t t1 = 0; t1 < taskOptionList.size(); t1++)
            {
                for (size_t t2 = 0; t2 < taskOptionList.size(); t2++)
                {
                    if (t1 != t2)
                    {
                        auto option1 = taskOptionList.at(t1);
                        auto option2 = taskOptionList.at(t2);

                        // build map from request to full task/option information
                        AggregatorTaskOptionPair* top = new AggregatorTaskOptionPair(vehicleId, option1->getTaskID(), option1->getOptionID(), option2->getTaskID(), option2->getOptionID());
                        m_routeTaskPairing[m_routeId] = std::shared_ptr<AggregatorTaskOptionPair>(top);

                        uxas::messages::route::RouteConstraints* r = new uxas::messages::route::RouteConstraints;
                        r->setStartLocation(option1->getEndLocation()->clone());
                        r->setStartHeading(option1->getEndHeading());
                        r->setEndLocation(option2->getStartLocation()->clone());
                        r->setEndHeading(option2->getStartHeading());
                        r->setRouteID(m_routeId);
                        planRequest->getRouteRequests().push_back(r);
                        m_pendingAutoReq[reqId].insert(m_routeId);
                        m_routeId++;
                    }
                }
            }

            // send this plan request to the prescribed route planner for ground vehicles
            if (m_groundVehicles.find(vehicleId) != m_groundVehicles.end())
            {
                sendGroundPlanRequest.push_back(planRequest);
            }
            else
            {
                sendAirPlanRequest.push_back(planRequest);
            }
        }
    }

    // send all requests for aircraft plans
    for (size_t k = 0; k < sendAirPlanRequest.size(); k++)
    {
        std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(sendAirPlanRequest.at(k));
        sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::AircraftPathPlanner(), pRequest);
    }

    // send all requests for ground plans
    for (size_t k = 0; k < sendGroundPlanRequest.size(); k++)
    {
        std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(sendGroundPlanRequest.at(k));
        if (m_fastPlan)
        {
            // short-circuit and just plan with straight line planner
            EuclideanPlan(sendGroundPlanRequest.at(k));
        }
        else
        {
            // send externally
            sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::GroundPathPlanner(), pRequest);
        }
    }

    // fast planning should be complete, so kick off sending response
    if (m_fastPlan)
    {
        CheckAllRoutePlans();
    }
}

void RouteAggregatorService::HandleRouteRequest(std::shared_ptr<uxas::messages::route::RouteRequest> request)
{
    if (request->getVehicleID().empty())
    {
        request->getVehicleID().reserve(m_entityStates.size());
        for (const auto& v : m_entityStates)
        {
            request->getVehicleID().push_back(v.second->getID());
        }
    }

    for (const int64_t& vehicleId : request->getVehicleID())
    {
        // create a new route plan request
        std::shared_ptr<uxas::messages::route::RoutePlanRequest> planRequest(new uxas::messages::route::RoutePlanRequest);
        planRequest->setAssociatedTaskID(request->getAssociatedTaskID());
        planRequest->setIsCostOnlyRequest(request->getIsCostOnlyRequest());
        planRequest->setOperatingRegion(request->getOperatingRegion());
        planRequest->setVehicleID(vehicleId);
        planRequest->setRequestID(m_routeRequestId);

        m_pendingRoute[request->getRequestID()].insert(m_routeRequestId);
        m_routeRequestId++;

        for (auto& r : request->getRouteRequests())
        {
            planRequest->getRouteRequests().push_back(r->clone());
        }


        std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(planRequest);
        if (m_groundVehicles.find(vehicleId) != m_groundVehicles.end())
        {
            if (m_fastPlan)
            {
                // short-circuit and just plan with straight line planner
                EuclideanPlan(planRequest);
            }
            else
            {
                // send externally
                sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::GroundPathPlanner(), pRequest);
            }
        }
        else
        {
            // send to aircraft planner
            sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::AircraftPathPlanner(), pRequest);
        }
    }

    // if fast planning, then all routes should be complete; kick off response
    if (m_fastPlan)
    {
        CheckAllRoutePlans();
    }
}

void RouteAggregatorService::CheckAllRoutePlans()
{
    // check pending route requests
    auto i = m_pendingRoute.begin();
    while (i != m_pendingRoute.end())
    {
        bool isFulfilled = true;
        for (const int64_t& j : i->second)
        {
            if (m_routePlanResponses.find(j) == m_routePlanResponses.end())
            {
                isFulfilled = false;
                break;
            }
        }

        if (isFulfilled)
        {
            SendRouteResponse(i->first);
            i = m_pendingRoute.erase(i);
        }
        else
        {
            i++;
        }
    }

    // check pending automation requests
    auto k = m_pendingAutoReq.begin();
    while (k != m_pendingAutoReq.end())
    {
        bool isFulfilled = true;
        for (const int64_t& j : k->second)
        {
            if (m_routePlans.find(j) == m_routePlans.end())
            {
                isFulfilled = false;
                break;
            }
        }

        if (isFulfilled)
        {
            SendMatrix(k->first);
            // finished with this automation request, discard
            m_uniqueAutomationRequests.erase(k->first);
            k = m_pendingAutoReq.erase(k);
        }
        else
        {
            k++;
        }
    }
}

void RouteAggregatorService::SendRouteResponse(int64_t routeKey)
{
    auto response = std::shared_ptr<uxas::messages::route::RouteResponse>(new uxas::messages::route::RouteResponse);
    response->setResponseID(routeKey);
    response->getRoutes().reserve(m_pendingRoute[routeKey].size());
    for (auto& rId : m_pendingRoute[routeKey])
    {
        auto plan = m_routePlanResponses.find(rId);
        if (plan != m_routePlanResponses.end())
        {
            response->getRoutes().push_back(plan->second->clone());

            // delete all individual routes from storage
            for (auto& i : plan->second->getRouteResponses())
            {
                m_routePlans.erase(i->getRouteID());
            }
            m_routePlanResponses.erase(plan);
        }
    }

    // send the results of the query
    std::shared_ptr<avtas::lmcp::Object> pResponse = std::static_pointer_cast<avtas::lmcp::Object>(response);
    sendSharedLmcpObjectBroadcastMessage(pResponse);
}

void RouteAggregatorService::SendMatrix(int64_t autoKey)
{
    auto matrix = std::shared_ptr<uxas::messages::task::AssignmentCostMatrix>(new uxas::messages::task::AssignmentCostMatrix);
    auto& areq = m_uniqueAutomationRequests[autoKey];
    matrix->setCorrespondingAutomationRequestID(areq->getRequestID());
    matrix->setOperatingRegion(areq->getOriginalRequest()->getOperatingRegion());
    matrix->setTaskLevelRelationship(areq->getOriginalRequest()->getTaskRelationships());
    matrix->getTaskList().assign(areq->getOriginalRequest()->getTaskList().begin(), areq->getOriginalRequest()->getTaskList().end());

    std::stringstream routesNotFound;
    for (auto& rId : m_pendingAutoReq[autoKey])
    {
        auto plan = m_routePlans.find(rId);
        if (plan != m_routePlans.end())
        {
            auto taskpair = m_routeTaskPairing.find(rId);
            if (taskpair != m_routeTaskPairing.end())
            {
                if (plan->second.second->getRouteCost() < 0)
                {
                    routesNotFound << "V[" << taskpair->second->vehicleId << "](" << taskpair->second->prevTaskId << "," << taskpair->second->prevTaskOption << ")-(" << taskpair->second->taskId << "," << taskpair->second->taskOption << ")" << std::endl;
                }
                auto toc = new uxas::messages::task::TaskOptionCost;
                toc->setDestinationTaskID(taskpair->second->taskId);
                toc->setDestinationTaskOption(taskpair->second->taskOption);
                toc->setIntialTaskID(taskpair->second->prevTaskId);
                toc->setIntialTaskOption(taskpair->second->prevTaskOption);
                toc->setTimeToGo(plan->second.second->getRouteCost());
                toc->setVehicleID(taskpair->second->vehicleId);
                matrix->getCostMatrix().push_back(toc);
                m_routeTaskPairing.erase(taskpair);
            }

            // clear out memory
            m_routePlanResponses.erase(plan->second.first);
            m_routePlans.erase(plan);
        }
    }

    // send the total cost matrix
    std::shared_ptr<avtas::lmcp::Object> pResponse = std::static_pointer_cast<avtas::lmcp::Object>(matrix);
    sendSharedLmcpObjectBroadcastMessage(pResponse);

    // clear out old options
    m_taskOptions.clear();

    if (!routesNotFound.str().empty())
    {
        auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
        serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
        auto keyValuePair = new afrl::cmasi::KeyValuePair;
        keyValuePair->setKey(std::string("RoutesNotFound - [VehicleId](StartTaskId,StartOptionId)-(EndTaskId,EndOptionId)"));
        keyValuePair->setValue(routesNotFound.str());
        serviceStatus->getInfo().push_back(keyValuePair);
        keyValuePair = nullptr;
        sendSharedLmcpObjectBroadcastMessage(serviceStatus);
        std::cout << "RoutesNotFound - [VehicleId](StartTaskId,StartOptionId)-(EndTaskId,EndOptionId) :: " << std::endl << routesNotFound.str() << std::endl << std::endl;
    }
    else
    {
        auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
        serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
        auto keyValuePair = new afrl::cmasi::KeyValuePair;
        keyValuePair->setKey(std::string("AssignmentMatrix - full"));
        serviceStatus->getInfo().push_back(keyValuePair);
        keyValuePair = nullptr;
        sendSharedLmcpObjectBroadcastMessage(serviceStatus);
    }


}

void RouteAggregatorService::EuclideanPlan(std::shared_ptr<uxas::messages::route::RoutePlanRequest> request)
{
    uxas::common::utilities::CUnitConversions flatEarth;
    int64_t regionId = request->getOperatingRegion();
    int64_t vehicleId = request->getVehicleID();
    int64_t taskId = request->getAssociatedTaskID();

    double speed = 1.0; // default if no speed available
    if (m_entityConfigurations.find(vehicleId) != m_entityConfigurations.end())
    {
        double speed = m_entityConfigurations[vehicleId]->getNominalSpeed();
        if (speed < 1e-2)
        {
            speed = 1.0; // default to 1 if too small for division
        }
    }

    auto response = std::shared_ptr<uxas::messages::route::RoutePlanResponse>(new uxas::messages::route::RoutePlanResponse);
    response->setAssociatedTaskID(taskId);
    response->setOperatingRegion(regionId);
    response->setVehicleID(vehicleId);
    response->setResponseID(request->getRequestID());

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
        plan->setRouteCost(linedist / speed * 1000); // milliseconds to arrive
        m_routePlans[routeId] = std::make_pair(request->getRequestID(), std::shared_ptr<uxas::messages::route::RoutePlan>(plan));
    }
    m_routePlanResponses[response->getResponseID()] = response;
}
}; //namespace service
}; //namespace uxas

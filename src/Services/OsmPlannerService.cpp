// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_OSM_Planner.cpp
 * Author: steve
 *
 * Created on September 25, 2015, 4:47 PM
 *
 */


#include "OsmPlannerService.h"

#include "Position.h"   //V_POSITION_t
#include "Waypoint.h"
//#include "Vehicle.h"
#include "PathInformation.h"
#include "FileSystemUtilities.h"
#include "Constants/UxAS_String.h"

#include "Constants/Convert.h"

#include "pugixml.hpp"

#include <sstream>  //stringstream
#include <chrono>       // time functions

//TODO:: read in a open street map and calculate it's visibility graph



#define STRING_COMPONENT_NAME "OSM_Planner"

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_COMPONENT_TYPE "OSM_Planner"
#define STRING_XML_OSM_FILE "OsmFile"
#define STRING_XML_MAP_EDGES_FILE "MapEdgesFile"
#define STRING_XML_SHORTEST_PATH_FILE "ShortestPathFile"
#define STRING_XML_METRICS_FILE "MetricsFile"


#define CIRCLE_BOUNDARY_INCREMENT (_PI_O_10)

namespace uxas
{
namespace service
{
OsmPlannerService::ServiceBase::CreationRegistrar<OsmPlannerService>
OsmPlannerService::s_registrar(OsmPlannerService::s_registryServiceTypeNames());

OsmPlannerService::OsmPlannerService()
: ServiceBase(OsmPlannerService::s_typeName(), OsmPlannerService::s_directoryName())
{
    m_strSavePath = "OsmPlannerService";
};

OsmPlannerService::~OsmPlannerService() { };

bool
OsmPlannerService::configure(const pugi::xml_node& ndComponent)
{
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    bool isSuccessful(true);



    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();
    //assert(strComponentType==STRING_XML_COMPONENT_TYPE)

    if (!ndComponent.attribute(STRING_XML_MAP_EDGES_FILE).empty())
    {
        m_mapEdgesFileName = ndComponent.attribute(STRING_XML_MAP_EDGES_FILE).value();
    }

    if (!ndComponent.attribute(STRING_XML_SHORTEST_PATH_FILE).empty())
    {
        m_shortestPathFileName = ndComponent.attribute(STRING_XML_SHORTEST_PATH_FILE).value();
    }

    if (!ndComponent.attribute(STRING_XML_METRICS_FILE).empty())
    {
        std::string metricsFileName = ndComponent.attribute(STRING_XML_METRICS_FILE).value();
        isSuccessful = uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(metricsFileName, m_strSavePath, m_searchMetricsFileName);
        if (isSuccessful)
        {
            std::ofstream metricsStream(m_searchMetricsFileName.c_str(), std::ios::trunc);
            metricsStream << "'number_highways', "
                    << "'number_nodes', "
                    << "'number_planning_nodes', "
                    << "'number_planning_edges', "
                    << "'process_map_time_s', "
                    << "'from_node_id', "
                    << "'to_node_id', "
                    << "'number_shortest_path_nodes', "
                    << "'number_waypoints', "
                    << "'shortest_path_cost', "
                    << "'search_time_s', "
                    << "'process_plan_time_s', "
                    << std::endl;
            metricsStream.close();
        }
        else
        {
            m_searchMetricsFileName.clear();
        }
    }

    if (!ndComponent.attribute(STRING_XML_OSM_FILE).empty())
    {
        m_osmFileName = ndComponent.attribute(STRING_XML_OSM_FILE).value();
        UXAS_LOG_INFORM("**** Reading and processing OSM File [", m_osmFileName, "] ****");

        isSuccessful = isBuildRoadGraphWithOsm(m_osmFileName);
        if (!isSuccessful)
        {
            sstrErrors << "ERROR:: **OsmPlannerService::bConfigure failed: could build road graph with osmFileName[" << m_osmFileName << "]" << std::endl;
            std::cout << sstrErrors.str();
        }
    }

    // ground planner does not respond to 'global' route requests
    // however, it will respond to route requests that are sent in a limited-cast fashion
    //addSubscriptionAddress(uxas::messages::route::RoutePlanRequest::Subscription);
    addSubscriptionAddress(uxas::common::MessageGroup::GroundPathPlanner());

    // need to keep track of all ground vehicles and their configurations for proper speed setting
    addSubscriptionAddress(afrl::vehicles::GroundVehicleConfiguration::Subscription);

    // only the ground planner can fulfill this request, response (as typical) will be limited-cast back
    addSubscriptionAddress(uxas::messages::route::EgressRouteRequest::Subscription);

    // subscribe, but only sends response for ground vehicles
    addSubscriptionAddress(uxas::messages::route::RoutePlanRequest::Subscription);

    // returns LineOfInterest, does not depend on entity configuration 
    addSubscriptionAddress(uxas::messages::route::RoadPointsRequest::Subscription);

    return (isSuccessful);
}

bool
OsmPlannerService::initialize()
{
    bool isSuccess(true);

    return (isSuccess);
};

bool
OsmPlannerService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    if (uxas::messages::route::isRoutePlanRequest(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<uxas::messages::route::RoutePlanRequest> request = std::static_pointer_cast<uxas::messages::route::RoutePlanRequest>(receivedLmcpMessage->m_object);
        //assumes only ground vehicles
        if (m_entityConfigurations.find(request->getVehicleID()) != m_entityConfigurations.end())
        {

            auto routePlanResponse = std::make_shared<uxas::messages::route::RoutePlanResponse>();
            routePlanResponse->setResponseID(request->getRequestID());
            bProcessRoutePlanRequest(request, routePlanResponse);
            auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(routePlanResponse);
            sendSharedLmcpObjectLimitedCastMessage(
                                                   getNetworkClientUnicastAddress(
                                                                                  receivedLmcpMessage->m_attributes->getSourceEntityId(),
                                                                                  receivedLmcpMessage->m_attributes->getSourceServiceId()
                                                                                  ),
                                                   newResponse);

        }
    }
    else if (uxas::messages::route::isRoadPointsRequest(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<uxas::messages::route::RoadPointsRequest> request =
                std::static_pointer_cast<uxas::messages::route::RoadPointsRequest>(receivedLmcpMessage->m_object);
        auto roadPointsResponse = std::make_shared<uxas::messages::route::RoadPointsResponse>();
        if (isProcessRoadPointsRequest(request, roadPointsResponse))
        {
            sendSharedLmcpObjectLimitedCastMessage(
                                                   getNetworkClientUnicastAddress(
                                                                                  receivedLmcpMessage->m_attributes->getSourceEntityId(),
                                                                                  receivedLmcpMessage->m_attributes->getSourceServiceId()
                                                                                  ),
                                                   roadPointsResponse);
        }
    }
    else if (uxas::messages::route::isEgressRouteRequest(receivedLmcpMessage->m_object))
    {
        auto egressResponse = std::make_shared<uxas::messages::route::EgressRouteResponse>();
        if (bProcessEgressRequest(std::static_pointer_cast<uxas::messages::route::EgressRouteRequest>(receivedLmcpMessage->m_object), egressResponse))
        {
            auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(egressResponse);
            sendSharedLmcpObjectLimitedCastMessage(
                                                   getNetworkClientUnicastAddress(
                                                                                  receivedLmcpMessage->m_attributes->getSourceEntityId(),
                                                                                  receivedLmcpMessage->m_attributes->getSourceServiceId()
                                                                                  ),
                                                   newResponse);
        }
    }

    else if (afrl::vehicles::isGroundVehicleConfiguration(receivedLmcpMessage->m_object.get()))
    {
        auto config = std::static_pointer_cast<afrl::vehicles::GroundVehicleConfiguration>(receivedLmcpMessage->m_object);
        m_entityConfigurations[config->getID()] = config;
    }
    else
    {
        UXAS_LOG_INFORM("WARNING::Unknown Message Type Encountered ptr_Object->getLmcpTypeName()[", receivedLmcpMessage->m_object->getFullLmcpTypeName(), "]");
    }
    return (false); // always false implies never terminating service from here
};

bool OsmPlannerService::bProcessEgressRequest(const std::shared_ptr<uxas::messages::route::EgressRouteRequest>& egressRequest,
                                              std::shared_ptr<uxas::messages::route::EgressRouteResponse>& egressResponse)
{
    /*
    // TODO: make this real, send two vehicles to the cordon location
    egressResponse->getHeadings().push_back(0.0f);
    egressResponse->getHeadings().push_back(180.0f);

    egressResponse->getNodeLocations().push_back(egressRequest->getStartLocation()->clone());
    egressResponse->getNodeLocations().push_back(egressRequest->getStartLocation()->clone());

    return true;
     */

    std::vector<n_FrameworkLib::CPosition> intersections;
    n_FrameworkLib::CPosition center(egressRequest->getStartLocation()->getLatitude() * n_Const::c_Convert::dDegreesToRadians(),
                                     egressRequest->getStartLocation()->getLongitude() * n_Const::c_Convert::dDegreesToRadians(),
                                     egressRequest->getStartLocation()->getAltitude(), m_flatEarth);

    findRoadIntersectionsOfCircle(center, egressRequest->getRadius(), intersections);

    for (auto i : intersections)
    {
        // TODO: figure out headings
        egressResponse->getHeadings().push_back(0.0f);

        afrl::cmasi::Location3D* loc = new afrl::cmasi::Location3D;
        loc->setLatitude(i.m_latitude_rad * n_Const::c_Convert::dRadiansToDegrees());
        loc->setLongitude(i.m_longitude_rad * n_Const::c_Convert::dRadiansToDegrees());
        loc->setAltitude(i.m_altitude_m);

        egressResponse->getNodeLocations().push_back(loc);
    }
    egressResponse->setResponseID(egressRequest->getRequestID());

    return true;
}

bool OsmPlannerService::bProcessRoutePlanRequest(const std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest,
                                                 std::shared_ptr<uxas::messages::route::RoutePlanResponse>& routePlanResponse)
{
    bool isSuccess(true);
    routePlanResponse->setAssociatedTaskID(routePlanRequest->getAssociatedTaskID());
    routePlanResponse->setOperatingRegion(routePlanRequest->getOperatingRegion());
    routePlanResponse->setVehicleID(routePlanRequest->getVehicleID());



    // extract route speed
    double speed = 1.0; // default to just distance
    if (m_entityConfigurations.find(routePlanRequest->getVehicleID()) != m_entityConfigurations.end())
    {
        speed = m_entityConfigurations[routePlanRequest->getVehicleID()]->getNominalSpeed();
        if (speed < 1.0)
        {
            speed = 1.0;
        }
    }

    for (auto itRequest = routePlanRequest->getRouteRequests().begin();
            itRequest != routePlanRequest->getRouteRequests().end();
            itRequest++)
    {
        auto routePlan = new uxas::messages::route::RoutePlan;
        routePlan->setRouteID((*itRequest)->getRouteID());
        routePlan->setRouteCost(-1);

        if (m_graph && m_planningIndexVsNodeId && m_idVsNode)
        {
            auto startTime = std::chrono::system_clock::now();

            std::vector<int64_t> waypointNodeIds;

            n_FrameworkLib::CPosition positionStart((*itRequest)->getStartLocation()->getLatitude() * n_Const::c_Convert::dDegreesToRadians(),
                                                    (*itRequest)->getStartLocation()->getLongitude() * n_Const::c_Convert::dDegreesToRadians(),
                                                    0.0, m_flatEarth);
            int64_t nodeIdStart(-1);
            double lengthFromStartToNode(-1.0);

            n_FrameworkLib::CPosition positionEnd((*itRequest)->getEndLocation()->getLatitude() * n_Const::c_Convert::dDegreesToRadians(),
                                                  (*itRequest)->getEndLocation()->getLongitude() * n_Const::c_Convert::dDegreesToRadians(),
                                                  0.0, m_flatEarth);
            int64_t nodeIdEnd(-1);
            double lengthFromNodeToEnd(-1.0);

            // start node Id
            bool isFoundNodeIdStart = isFindClosestNodeId(positionStart, m_cellVsPlanningNodeIds, nodeIdStart, lengthFromStartToNode);
            // end node Id
            bool isFoundNodeIdEnd = isFindClosestNodeId(positionEnd, m_cellVsPlanningNodeIds, nodeIdEnd, lengthFromNodeToEnd);
            if (isFoundNodeIdStart && isFoundNodeIdEnd)
            {
                int32_t numberWaypoints(-1); // for metrics
                int32_t pathCost(0);
                std::deque<int64_t> pathNodeIds;
                if (isFindShortestRoute(nodeIdStart, nodeIdEnd, pathCost, pathNodeIds))
                {
                    float routCost = (static_cast<float> (lengthFromStartToNode) +
                            static_cast<float> (lengthFromNodeToEnd) +
                            static_cast<float> (pathCost)) / speed;
                    routePlan->setRouteCost(routCost * 1000); //convert to ms

                    if (!routePlanRequest->getIsCostOnlyRequest())
                    {
                        int64_t waypointNumber(0);

                        // add start point
                        waypointNumber++;
                        auto waypoint = new afrl::cmasi::Waypoint();
                        waypoint->setNumber(waypointNumber);
                        // nextWaypoint set when following waypoint is added
                        waypoint->setSpeed(speed);
                        waypoint->setTurnType(afrl::cmasi::TurnType::FlyOver);
                        waypoint->setLatitude(positionStart.m_latitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                        waypoint->setLongitude(positionStart.m_longitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                        waypoint->setAltitude(positionStart.m_altitude_m);
                        routePlan->getWaypoints().push_back(waypoint);
                        waypoint = nullptr; // gave up ownership


                        //add rest of points
                        // for each point in the plan:
                        // - find the way and the points associated with it
                        // - locate the start and end of the section of the way that is bracketed by the current and next plan points
                        // - add this section to the plan
                        auto itNextPathNodeId = pathNodeIds.begin();
                        if (!pathNodeIds.empty())
                        {
                            itNextPathNodeId++; // need the 'next' waypoint in the list to find the end of the path section
                        }
                        for (auto itPathNodeId = pathNodeIds.begin(); itPathNodeId != pathNodeIds.end(); itPathNodeId++)
                        {
                            if (itNextPathNodeId != pathNodeIds.end())
                            {
                                // find the planning edge
                                auto itPlanningEdge = m_nodeIdsVsEdgeNodeIds.find(std::make_pair(*itPathNodeId, *itNextPathNodeId));
                                if (itPlanningEdge != m_nodeIdsVsEdgeNodeIds.end())
                                {
                                    for (auto itNodeId = itPlanningEdge->second->m_nodeIds.begin(); itNodeId != itPlanningEdge->second->m_nodeIds.end(); itNodeId++)
                                    {
                                        // add each point of the section
                                        auto itNewNode = m_idVsNode->find(*itNodeId);
                                        if (itNewNode != m_idVsNode->end())
                                        {
                                            //NOTE:: not setting AltitudeType, Number, NextWaypoint, Speed, SpeedType, ClimbRate, TurnType, VehicleActionList, ContingencyWaypointA, ContingencyWaypointB, AssociatedTasks
                                            //NOTE:: only setting Latitude, Longitude, Altitude  :)
                                            waypointNumber++;
                                            routePlan->getWaypoints().back()->setNextWaypoint(waypointNumber);
                                            waypoint = new afrl::cmasi::Waypoint();
                                            waypoint->setNumber(waypointNumber);
                                            waypoint->setSpeed(speed);
                                            waypoint->setTurnType(afrl::cmasi::TurnType::FlyOver);
                                            waypoint->setLatitude(itNewNode->second->m_latitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                                            waypoint->setLongitude(itNewNode->second->m_longitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                                            waypoint->setAltitude(itNewNode->second->m_altitude_m);
                                            routePlan->getWaypoints().push_back(waypoint);
                                            waypoint = nullptr; // gave up ownership

                                            waypointNodeIds.push_back(*itNodeId);
                                        }
                                        else
                                        {
                                            UXAS_LOG_ERROR("bProcessRoutePlanRequest:: while building plan:: could not find node with the Id[", *itNodeId, "]");
                                            isSuccess = false;
                                            break;
                                        }
                                    }
                                }
                                else
                                {
                                    UXAS_LOG_ERROR("bProcessRoutePlanRequest:: while building plan:: could not find the planning edge for node Id's [", *itPathNodeId, "] and [", *itNextPathNodeId, "]");
                                    isSuccess = false;
                                    //break;
                                }
                            }
                            else
                            {
                                // single node, just add it
                                auto itNewNode = m_idVsNode->find(*itPathNodeId);
                                if (itNewNode != m_idVsNode->end())
                                {
                                    //NOTE:: not setting AltitudeType, SpeedType, ClimbRate, VehicleActionList, ContingencyWaypointA, ContingencyWaypointB, AssociatedTasks
                                    //NOTE:: only setting Latitude, Longitude, Altitude, Number, NextWaypoint, Speed, TurnType  :)
                                    waypointNumber++;
                                    routePlan->getWaypoints().back()->setNextWaypoint(waypointNumber);
                                    waypoint = new afrl::cmasi::Waypoint();
                                    waypoint->setNumber(waypointNumber);
                                    waypoint->setSpeed(speed);
                                    waypoint->setTurnType(afrl::cmasi::TurnType::FlyOver);
                                    waypoint->setLatitude(itNewNode->second->m_latitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                                    waypoint->setLongitude(itNewNode->second->m_longitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                                    waypoint->setAltitude(itNewNode->second->m_altitude_m);
                                    routePlan->getWaypoints().push_back(waypoint);
                                    waypoint = nullptr; // gave up ownership

                                    waypointNodeIds.push_back(*itPathNodeId);
                                }
                                else
                                {
                                    UXAS_LOG_ERROR("bProcessRoutePlanRequest:: while building plan:: could not find node with the Id[", *itPathNodeId, "]");
                                    isSuccess = false;
                                    break;
                                }
                            } //for(auto itPathNodeId=pathNodeIds.begin();itPathNodeId!=pathNodeIds.end();itPathNodeId++)
                            if (itNextPathNodeId != pathNodeIds.end())
                            {
                                itNextPathNodeId++;
                            }
                        }
                        // add end point
                        waypointNumber++;
                        routePlan->getWaypoints().back()->setNextWaypoint(waypointNumber);
                        waypoint = new afrl::cmasi::Waypoint();
                        waypoint->setNumber(waypointNumber);
                        waypoint->setNextWaypoint(waypointNumber);
                        waypoint->setSpeed(speed);
                        waypoint->setTurnType(afrl::cmasi::TurnType::FlyOver);
                        waypoint->setLatitude(positionEnd.m_latitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                        waypoint->setLongitude(positionEnd.m_longitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                        waypoint->setAltitude(positionEnd.m_altitude_m);
                        routePlan->getWaypoints().push_back(waypoint);
                        waypoint = nullptr; // gave up ownership
                    }
                    numberWaypoints = routePlan->getWaypoints().size();
                }
                else
                {
                    UXAS_LOG_ERROR("Error:: could not find route for RouteRequestId[", (*itRequest)->getRouteID(), "].");
                    isSuccess = false;
                }

                if (!m_shortestPathFileName.empty())
                {
                    std::string shortestPathPathFileName;
                    if (uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(m_shortestPathFileName, m_strSavePath, shortestPathPathFileName))
                    {
                        std::ofstream shortestPathStream(shortestPathPathFileName.c_str());
                        shortestPathStream << "'node_id_1','edge_north_01','edge_east_01','edge_alt_01','node_id_2','edge_north_02','edge_east_02','edge_alt_02','edge_length_f'" << std::endl;
                        auto itNodeOne = waypointNodeIds.begin();
                        auto itNodeTwo = waypointNodeIds.begin();
                        if (!waypointNodeIds.empty())
                        {
                            itNodeTwo++;
                        }
                        for (; itNodeTwo != waypointNodeIds.end(); itNodeOne++, itNodeTwo++)
                        {
                            auto itNode_1 = m_idVsNode->find(*itNodeOne);
                            auto itNode_2 = m_idVsNode->find(*itNodeTwo);
                            if ((itNode_1 != m_idVsNode->end()) &&
                                    (itNode_2 != m_idVsNode->end()))
                            {

                                shortestPathStream << *itNodeOne;
                                shortestPathStream << ",";
                                shortestPathStream << *(itNode_1->second);
                                shortestPathStream << ",";
                                shortestPathStream << *itNodeTwo;
                                shortestPathStream << ",";
                                shortestPathStream << *(itNode_2->second);
                                shortestPathStream << ",";
                                shortestPathStream << 0;
                                shortestPathStream << std::endl;
                            }
                        }
                        shortestPathStream.close();
                    } //if (uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(m_shortestPa ...
                } //if(!m_shortestPathFileName.empty())

                auto endTime = std::chrono::system_clock::now();
                std::chrono::duration<double> elapsed_seconds = endTime - startTime;
                m_processPlanTime_s = elapsed_seconds.count();

                if (!m_searchMetricsFileName.empty())
                {
                    std::ofstream metricsStream(m_searchMetricsFileName.c_str(), std::ios::app);
                    metricsStream << m_numberHighways << ", "
                            << m_numberNodes << ", "
                            << m_numberPlanningNodes << ", "
                            << m_numberPlanningEdges << ", "
                            << m_processMapTime_s << ", "
                            << nodeIdStart << ", "
                            << nodeIdEnd << ", "
                            << pathNodeIds.size() << ", "
                            << numberWaypoints << ", "
                            << pathCost << ", "
                            << m_searchTime_s << ", "
                            << m_processPlanTime_s
                            << std::endl;
                    metricsStream.close();
                } //if(!m_searchMetricsFileName.empty())
            }
            else //if(isFindClosestIndices(positionStart,positionEnd,indexIdStart,index ...
            {
                UXAS_LOG_WARN("bProcessRoutePlanRequest:: could not find graph indices for RouteRequestId[", (*itRequest)->getRouteID(), "].");
                isSuccess = false;
            } //if(isFindClosestIndices(positionStart,positionEnd,indexIdStart,index  ...
        } //if(m_graph && m_planningIndexVsNodeId && m_idVsNode)
        routePlanResponse->getRouteResponses().push_back(routePlan);
        routePlan = nullptr; //gave it up
    } //for (auto itRequest = routePlanRequest->getRouteRequests()

    return (isSuccess);
}

bool OsmPlannerService::isProcessRoadPointsRequest(const std::shared_ptr<uxas::messages::route::RoadPointsRequest>& roadPointsRequest,
                                                   std::shared_ptr<uxas::messages::route::RoadPointsResponse>& roadPointsResponse)
{
    bool isSuccess(true);
    if (m_graph && m_planningIndexVsNodeId && m_idVsNode)
    {
        roadPointsResponse->setResponseID(roadPointsRequest->getRequestID());
        for (auto itRequest = roadPointsRequest->getRoadPointsRequests().begin();
                itRequest != roadPointsRequest->getRoadPointsRequests().end();
                itRequest++)
        {
            auto startTime = std::chrono::system_clock::now();

            n_FrameworkLib::CPosition positionStart((*itRequest)->getStartLocation()->getLatitude() * n_Const::c_Convert::dDegreesToRadians(),
                                                    (*itRequest)->getStartLocation()->getLongitude() * n_Const::c_Convert::dDegreesToRadians(),
                                                    0.0, m_flatEarth);

            n_FrameworkLib::CPosition positionEnd((*itRequest)->getEndLocation()->getLatitude() * n_Const::c_Convert::dDegreesToRadians(),
                                                  (*itRequest)->getEndLocation()->getLongitude() * n_Const::c_Convert::dDegreesToRadians(),
                                                  0.0, m_flatEarth);
            int64_t nodeIdStart(-1);
            double lengthFromStartToNode_m(-1.0);
            int64_t nodeIdEnd(-1);
            double lengthFromNodeToEnd_m(-1.0);

            // 1) find closest nodes (from all nodes) to start and to end points
            // start node Id
            isSuccess &= isFindClosestNodeId(positionStart, m_cellVsAllNodeIds, nodeIdStart, lengthFromStartToNode_m);
            // end node Id
            isSuccess &= isFindClosestNodeId(positionEnd, m_cellVsAllNodeIds, nodeIdEnd, lengthFromNodeToEnd_m);

            if (isSuccess)
            {
                // need these here to be available for saving metrics
                std::vector<int64_t> fullPathNodeIds;


                // 2) find the edges that these nodes are part of
                // find all the segments with this node
                auto itSegmentsStart = m_nodeIdVsSegmentBeginEndIds.equal_range(nodeIdStart);
                auto itSegmentsEnd = m_nodeIdVsSegmentBeginEndIds.equal_range(nodeIdEnd);
                if ((itSegmentsStart.first != m_nodeIdVsSegmentBeginEndIds.end()) &&
                        (itSegmentsEnd.first != m_nodeIdVsSegmentBeginEndIds.end()))
                {
                    // 3) if they are on the same edge, get the points in the correct direction and build a path, done
                    bool isSameEdge(false);
                    int64_t edgeBeginNodeId(-1);
                    int64_t edgeEndNodeId(-1);
                    for (auto itEdgeIdStart = itSegmentsStart.first; itEdgeIdStart != itSegmentsStart.second; itEdgeIdStart++)
                    {
                        for (auto itEdgeIdEnd = itSegmentsEnd.first; itEdgeIdEnd != itSegmentsEnd.second; itEdgeIdEnd++)
                        {
//                            UXAS_LOG_INFORM("itEdgeIdStart->second.first[" << itEdgeIdStart->second.first
//                                               << "] itEdgeIdStart->second.second[" << itEdgeIdStart->second.second
//                                               << "] itEdgeIdEnd->second.first[" << itEdgeIdEnd->second.first
//                                               << "] itEdgeIdEnd->second.second[" << itEdgeIdEnd->second.second << "]");
                            if ((itEdgeIdStart->second.first == itEdgeIdEnd->second.first) &&
                                    (itEdgeIdStart->second.second == itEdgeIdEnd->second.second))
                            {
                                edgeBeginNodeId = itEdgeIdStart->second.first;
                                edgeEndNodeId = itEdgeIdStart->second.second;
                                isSameEdge = true;
                                break;
                            }
                        }
                        if (isSameEdge)
                        {
                            break;
                        }
                    }
                    if (isSameEdge)
                    {
                        // get order of planning nodes from start to end on the edge
                        // find the edge where start nodeIdStart is before nodeIdEnd

                        if (!isGetNodesOnSegment(std::make_pair(edgeBeginNodeId, edgeEndNodeId),
                                                 nodeIdStart, nodeIdEnd, true, fullPathNodeIds))
                        {
                            //try reverse edge
                            isGetNodesOnSegment(std::make_pair(edgeEndNodeId, edgeBeginNodeId),
                                                nodeIdStart, nodeIdEnd, true, fullPathNodeIds);
                        }
                        if (!fullPathNodeIds.empty())
                        {
                            // build the lineofinterest
                            afrl::impact::LineOfInterest * lineOfInterest(new afrl::impact::LineOfInterest);
                            lineOfInterest->setLineID((*itRequest)->getRoadPointsID());
                            for (auto roadNodeId : fullPathNodeIds)
                            {
                                auto itNewNode = m_idVsNode->find(roadNodeId);
                                if (itNewNode != m_idVsNode->end())
                                {
                                    afrl::cmasi::Location3D* loc = new afrl::cmasi::Location3D;
                                    loc->setLatitude(itNewNode->second->m_latitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                                    loc->setLongitude(itNewNode->second->m_longitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                                    loc->setAltitude(itNewNode->second->m_altitude_m);
                                    loc->setAltitudeType(afrl::cmasi::AltitudeType::AGL);
                                    lineOfInterest->getLine().push_back(loc);
                                    loc = nullptr;
                                }
                                else
                                {
                                    //TODO:: ERROR could not find node for id
                                    isSuccess = false;
                                    break;
                                }
                            }
                            if (isSuccess)
                            {
                                roadPointsResponse->getRoadPointsResponses().push_back(lineOfInterest);
                                lineOfInterest = nullptr;
                            }
                            else
                            {
                                delete lineOfInterest;
                                lineOfInterest = nullptr;
                            }
                        }
                    }
                    else //if(isSameEdge)
                    {
                        // 4) find distance from start/end points to edge point 
                        double distanceStartToStart_01((std::numeric_limits<double>::max)());
                        double distanceStartToStart_02((std::numeric_limits<double>::max)());
                        double distanceEndToEnd_01((std::numeric_limits<double>::max)());
                        double distanceEndToEnd_02((std::numeric_limits<double>::max)());

                        auto startSegmentNodeId_01 = itSegmentsStart.first->second.first;
                        auto startSegmentNodeId_02 = itSegmentsStart.first->second.second;
                        auto endSegmentNodeId_01 = itSegmentsEnd.first->second.first;
                        auto endSegmentNodeId_02 = itSegmentsEnd.first->second.second;

                        // TODO:: these are euclidean, need to get the distance along the path
                        auto itNewNode = m_idVsNode->find(startSegmentNodeId_01);
                        if (itNewNode != m_idVsNode->end())
                        {
                            distanceStartToStart_01 = positionStart.relativeDistance2D_m(*(itNewNode->second));
                        }
                        else
                        {
                            //TODO:: ERROR could not find node from id
                        }
                        itNewNode = m_idVsNode->find(startSegmentNodeId_02);
                        if (itNewNode != m_idVsNode->end())
                        {
                            distanceStartToStart_02 = positionStart.relativeDistance2D_m(*(itNewNode->second));
                        }
                        else
                        {
                            //TODO:: ERROR could not find node from id
                        }
                        itNewNode = m_idVsNode->find(endSegmentNodeId_01);
                        if (itNewNode != m_idVsNode->end())
                        {
                            distanceEndToEnd_01 = positionEnd.relativeDistance2D_m(*(itNewNode->second));
                        }
                        else
                        {
                            //TODO:: ERROR could not find node from id
                        }
                        itNewNode = m_idVsNode->find(endSegmentNodeId_02);
                        if (itNewNode != m_idVsNode->end())
                        {
                            distanceEndToEnd_02 = positionEnd.relativeDistance2D_m(*(itNewNode->second));
                        }
                        else
                        {
                            //TODO:: ERROR could not find node from id
                        }

                        // 5) find four shortest paths from the combination of start/end nodes
                        // 6) choose pair of nodes that implement the shortest path (include start/end distances)

                        int32_t pathCostFinal(INT32_MAX);
                        int32_t pathCost(INT32_MAX);
                        std::deque<int64_t> pathNodeIds;
                        std::deque<int64_t> pathNodeIdsFinal;
                        if(isGetRoadPoints(startSegmentNodeId_01,endSegmentNodeId_01,pathCost,pathNodeIds))
                        {
                            pathCost += static_cast<int32_t> (distanceStartToStart_01 + distanceEndToEnd_01);
                            if (pathCost < pathCostFinal)
                            {
                                pathCostFinal = pathCost;
                                pathNodeIdsFinal = pathNodeIds;
                            }
                        }
                        if(isGetRoadPoints(startSegmentNodeId_01,endSegmentNodeId_02,pathCost,pathNodeIds))
                        {
                            pathCost += static_cast<int32_t> (distanceStartToStart_01 + distanceEndToEnd_02);
                            if (pathCost < pathCostFinal)
                            {
                                pathCostFinal = pathCost;
                                pathNodeIdsFinal = pathNodeIds;
                            }
                        }
                        if(isGetRoadPoints(startSegmentNodeId_02,endSegmentNodeId_01,pathCost,pathNodeIds))
                        {
                            pathCost += static_cast<int32_t> (distanceStartToStart_02 + distanceEndToEnd_01);
                            if (pathCost < pathCostFinal)
                            {
                                pathCostFinal = pathCost;
                                pathNodeIdsFinal = pathNodeIds;
                            }
                        }
                        if(isGetRoadPoints(startSegmentNodeId_02,endSegmentNodeId_02,pathCost,pathNodeIds))
                        {
                            pathCost += static_cast<int32_t> (distanceStartToStart_02 + distanceEndToEnd_02);
                            if (pathCost < pathCostFinal)
                            {
                                pathCostFinal = pathCost;
                                pathNodeIdsFinal = pathNodeIds;
                            }
                        }
                        

                        if (pathNodeIdsFinal.size() >= 1) // N--^--X-----X---^---N or N--^--X--^--N
                        {

                            // 7) build plan from closest start node to start node

                            //UXAS_LOG_INFORM("[startSegmentNodeId_01,startSegmentNodeId_02]=[" << startSegmentNodeId_01 << "," << startSegmentNodeId_02 << "]");
                            edgeEndNodeId = pathNodeIdsFinal.front();
                            edgeBeginNodeId = startSegmentNodeId_02;
                            if (edgeBeginNodeId == edgeEndNodeId)
                            {
                                edgeBeginNodeId = startSegmentNodeId_01;
                            }

                            //UXAS_LOG_INFORM("[edgeBeginNodeId,edgeEndNodeId]=[" << edgeBeginNodeId << "," << edgeEndNodeId << "]");
                            if (isGetNodesOnSegment(std::make_pair(edgeBeginNodeId, edgeEndNodeId),
                                                    nodeIdStart, edgeEndNodeId, false, fullPathNodeIds))
                            {
                                // 8) build plan from start node to end node
                                auto itPathNodeIdLast = pathNodeIdsFinal.begin();
                                for (auto itPathNodeId = pathNodeIdsFinal.begin(); itPathNodeId != pathNodeIdsFinal.end(); itPathNodeId++)
                                {
                                    if (itPathNodeId != pathNodeIdsFinal.begin())
                                    {
                                        std::vector<int64_t> segmentPathNodeIds;
                                        if (isGetNodesOnSegment(std::make_pair(*itPathNodeIdLast, *itPathNodeId),
                                                                *itPathNodeIdLast, edgeEndNodeId, false, segmentPathNodeIds))
                                        {
                                            fullPathNodeIds.insert(fullPathNodeIds.end(), segmentPathNodeIds.begin(), segmentPathNodeIds.end());
                                        }
                                        else
                                        {
                                            UXAS_LOG_ERROR("ERROR::isProcessRoadPointsRequest nodes on segment not found for edge Node IDs[", *itPathNodeIdLast, ",", *itPathNodeId, "] start/end IDs [", *itPathNodeIdLast, ",", *itPathNodeId, "]");
                                            isSuccess = false;
                                        }
                                    }
                                    itPathNodeIdLast = itPathNodeId;
                                }
                                // 9) build plan from end node to closest end node

                                edgeBeginNodeId = pathNodeIdsFinal.back();
                                edgeEndNodeId = endSegmentNodeId_01;
                                if (edgeBeginNodeId == edgeEndNodeId)
                                {
                                    edgeEndNodeId = endSegmentNodeId_02;
                                }
                                std::vector<int64_t> segmentPathNodeIds;
                                if (isGetNodesOnSegment(std::make_pair(edgeBeginNodeId, edgeEndNodeId),
                                                        edgeBeginNodeId, nodeIdEnd, false, segmentPathNodeIds))
                                {
                                    fullPathNodeIds.insert(fullPathNodeIds.end(), segmentPathNodeIds.begin(), segmentPathNodeIds.end());
                                }
                                else
                                {
                                    UXAS_LOG_ERROR("ERROR::isProcessRoadPointsRequest nodes on segment not found for edge Node IDs[", edgeBeginNodeId, ",", edgeEndNodeId, "] start/end IDs [", edgeBeginNodeId, ",", edgeEndNodeId, "]");
                                    isSuccess = false;
                                }

                                // 10) build the lineofinterest
                                afrl::impact::LineOfInterest * lineOfInterest(new afrl::impact::LineOfInterest);
                                lineOfInterest->setLineID((*itRequest)->getRoadPointsID());
                                for (auto roadNodeId : fullPathNodeIds)
                                {
                                    auto itNewNode = m_idVsNode->find(roadNodeId);
                                    if (itNewNode != m_idVsNode->end())
                                    {
                                        afrl::cmasi::Location3D* loc = new afrl::cmasi::Location3D;
                                        loc->setLatitude(itNewNode->second->m_latitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                                        loc->setLongitude(itNewNode->second->m_longitude_rad * n_Const::c_Convert::dRadiansToDegrees());
                                        loc->setAltitude(itNewNode->second->m_altitude_m);
                                        loc->setAltitudeType(afrl::cmasi::AltitudeType::AGL);
                                        lineOfInterest->getLine().push_back(loc);
                                        loc = nullptr;
                                    }
                                    else
                                    {
                                        //TODO:: ERROR could not find node for id
                                        isSuccess = false;
                                        break;
                                    }
                                }
                                if (isSuccess)
                                {
                                    roadPointsResponse->getRoadPointsResponses().push_back(lineOfInterest);
                                    lineOfInterest = nullptr;
                                }
                                else
                                {
                                    delete lineOfInterest;
                                    lineOfInterest = nullptr;
                                }
                            }
                            else
                            {
                                UXAS_LOG_ERROR("ERROR::isProcessRoadPointsRequest nodes on segment not found for edge Node IDs[", edgeBeginNodeId, ",", edgeEndNodeId, "] start/end IDs [", nodeIdStart, ",", edgeEndNodeId, "]");
                                isSuccess = false;
                            }
                        } //if(pathNodeIds.size() > 1)

                    } //if (isSameEdge)
                } //if ((itSegmentsStart.first != m_nodeIdVsSegmentBeginEndIds.end())
                if (isSuccess)
                {
                    if (!m_shortestPathFileName.empty())
                    {
                        std::string shortestPathPathFileName;
                        if (uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(m_shortestPathFileName, m_strSavePath, shortestPathPathFileName))
                        {
                            std::ofstream shortestPathStream(shortestPathPathFileName.c_str());
                            shortestPathStream << "'node_id_1','edge_north_01','edge_east_01','edge_alt_01','node_id_2','edge_north_02','edge_east_02','edge_alt_02','edge_length_f'" << std::endl;
                            auto itNodeOne = fullPathNodeIds.begin();
                            auto itNodeTwo = fullPathNodeIds.begin();
                            if (!fullPathNodeIds.empty())
                            {
                                itNodeTwo++;
                            }
                            for (; itNodeTwo != fullPathNodeIds.end(); itNodeOne++, itNodeTwo++)
                            {
                                auto itNode_1 = m_idVsNode->find(*itNodeOne);
                                auto itNode_2 = m_idVsNode->find(*itNodeTwo);
                                if ((itNode_1 != m_idVsNode->end()) &&
                                        (itNode_2 != m_idVsNode->end()))
                                {

                                    shortestPathStream << *itNodeOne;
                                    shortestPathStream << ",";
                                    shortestPathStream << *(itNode_1->second);
                                    shortestPathStream << ",";
                                    shortestPathStream << *itNodeTwo;
                                    shortestPathStream << ",";
                                    shortestPathStream << *(itNode_2->second);
                                    shortestPathStream << ",";
                                    shortestPathStream << 0;
                                    shortestPathStream << std::endl;
                                }
                            }
                            shortestPathStream.close();
                        } //if (uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(m_shortestPa ...
                    } //if(!m_shortestPathFileName.empty())

                    auto endTime = std::chrono::system_clock::now();
                    std::chrono::duration<double> elapsed_seconds = endTime - startTime;
                    m_processPlanTime_s = elapsed_seconds.count();

                    if (!m_searchMetricsFileName.empty())
                    {
                        std::ofstream metricsStream(m_searchMetricsFileName.c_str(), std::ios::app);
                        metricsStream << m_numberHighways << ", "
                                << m_numberNodes << ", "
                                << m_numberPlanningNodes << ", "
                                << m_numberPlanningEdges << ", "
                                << m_processMapTime_s << ", "
                                << nodeIdStart << ", "
                                << nodeIdEnd << ", "
                                << fullPathNodeIds.size() << ", "
                                //<< pathCostFinal << ", "
                                << m_searchTime_s << ", "
                                << m_processPlanTime_s
                                << std::endl;
                        metricsStream.close();
                    } //if(!m_searchMetricsFileName.empty())
                } //if(isSuccess)
            }
            else //if (isSuccess)
            {
                UXAS_LOG_ERROR("Error:: could not find route for RouteRequestId[", (*itRequest)->getRoadPointsID(), "].");
                isSuccess = false;
            }
        } //for (auto itRequest = roadPoints
    } //if(m_graph && m_planningIndexVsNodeId && m_idVsNode)

    return (isSuccess);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

bool OsmPlannerService::isGetRoadPoints(const int64_t& startNodeId,const int64_t& endNodeId,int32_t& pathCost,std::deque<int64_t>& pathNodeIds)
{
    bool isSuccess{true};
    
    pathCost = INT32_MAX;
    pathNodeIds.clear();
    if (startNodeId != endNodeId)
    {
        if (!isFindShortestRoute(startNodeId, endNodeId, pathCost, pathNodeIds))
        {
            UXAS_LOG_ERROR("ERROR::isProcessRoadPointsRequest nodes on segment not found for edge Node IDs[", startNodeId, ",", endNodeId, "]");
            isSuccess = false;
        }
    }
    else
    {
        pathCost = 0;   //THIS IS THE COST OF THE INTERVENING SEGEMENTS
        pathNodeIds.clear();
        pathNodeIds.push_back(startNodeId);
    }
    return(isSuccess);
}
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

bool OsmPlannerService::isBuildRoadGraphWithOsm(const string & osmFile)
{
    bool isSuccess(true);

    auto startTime = std::chrono::system_clock::now();

    m_wayIdVsNodeId.clear();
    m_cellVsPlanningNodeIds.clear();
    m_cellVsAllNodeIds.clear();
    m_nodeIdsVsEdgeNodeIds.clear();
    m_nodeIdVsPlanningIndex.clear();
    m_planningIndexVsNodeId = std::make_shared<std::unordered_map<int32_t, int64_t> >();

    m_idVsNode = std::make_shared<std::unordered_map<int64_t, std::unique_ptr<n_FrameworkLib::CPosition> > >();
    m_edges.clear();

    pugi::xml_document xmldocConfiguration;
    std::ifstream ifsOperatorXML(osmFile);
    pugi::xml_parse_result result = xmldocConfiguration.load(ifsOperatorXML);

    if (result)
    {
        pugi::xml_node osmMap = xmldocConfiguration.child("osm");
        if (osmMap)
        {
            // TODO: use the map to sort out planning nodes
            std::unordered_map<int64_t, bool> nodeIdVs_isPlanningNode;
            std::vector<int64_t> highWayIds;

            // first get a list of the roads (highway's)
            for (pugi::xml_node ndCurrent = osmMap.child("way"); ndCurrent; ndCurrent = ndCurrent.next_sibling("way"))
            {
                if (!ndCurrent.attribute("id").empty())
                {
                    int64_t wayId = ndCurrent.attribute("id").as_int64();
                    bool isHighway(false);
                    std::vector<int64_t> nodes; // all the node associated with this way
                    for (pugi::xml_node wayNode = ndCurrent.first_child(); wayNode; wayNode = wayNode.next_sibling())
                    {
                        if (strcmp(wayNode.name(), "nd") == 0)
                        {
                            if (!wayNode.attribute("ref").empty())
                            {
                                nodes.push_back(wayNode.attribute("ref").as_int64());
                            }
                        }
                            // only save nodes and edges associated with highway's (i.e any road)
                        else if ((!isHighway) && (strcmp(wayNode.name(), "tag") == 0))
                        {
                            if (!wayNode.attribute("k").empty())
                            {
                                if (strcmp(wayNode.attribute("k").as_string(), "highway") == 0)
                                {
                                    isHighway = true;
                                }
                            }
                        }
                    }
                    if (isHighway)
                    {
                        highWayIds.push_back(wayId);

                        // the begin and end nodes for the highway
                        auto itHighwayFirst = nodes.begin();
                        auto itHighwayLast = nodes.end();
                        if (!nodes.empty())
                        {
                            itHighwayLast--; // last node on the highway
                        }

                        for (auto itNode = nodes.begin(); itNode != nodes.end(); itNode++)
                        {
                            // save all of the nodes associated with the Highway)
                            m_wayIdVsNodeId.insert(std::make_pair(wayId, *itNode));

                            // add all of the nodes associated with highway
                            // set nodes used for planning to true, others to false.
                            // Not all highway nodes are planning nodes
                            // only save begin and end and intersecting nodes
                            bool isPlanningNode(false);
                            if ((itNode == itHighwayFirst) || (itNode == itHighwayLast))
                            {
                                isPlanningNode = true;
                            }
                            else
                            {
                                auto itId_isPlanning = nodeIdVs_isPlanningNode.find(*itNode);
                                if (itId_isPlanning == nodeIdVs_isPlanningNode.end())
                                {
                                    // haven't encountered this node, so it is not a planning node, yet
                                    isPlanningNode = false;
                                }
                                else
                                {
                                    // have encountered this node, so it is a planning node
                                    isPlanningNode = true;
                                }
                            }
                            nodeIdVs_isPlanningNode[*itNode] = isPlanningNode;
                        } //for (auto itNode = nodes.begin(); itNode != nodes.end(); itNode++)
                    }
                }
                else //if (!ndCurrent.attribute("id").empty())
                {
                    UXAS_LOG_ERROR("OSM FILE:: parse XML string failed for osmFile[", osmFile, "] :: could not find a 'way id'");
                }
            }

            // next load all of the nodes associated with ways

            /*! \brief  storage for node Ids used in planning*/
            std::unordered_set<int64_t> planningNodeIds;
            int32_t planinngIndex(0); // an index based on the order of the node selected for planning

            double northMax_m((std::numeric_limits<double>::min)()); //find the bounding box
            double northMin_m((std::numeric_limits<double>::max)()); //find the bounding box
            double eastMax_m((std::numeric_limits<double>::min)()); //find the bounding box
            double eastMin_m((std::numeric_limits<double>::max)()); //find the bounding box

            for (pugi::xml_node ndCurrent = osmMap.child("node"); ndCurrent; ndCurrent = ndCurrent.next_sibling("node"))
            {
                //<node id="196779277" visible="true" version="2" changeset="2671787" timestamp="2009-09-29T01:02:14Z" user="woodpeck_fixbot" uid="147510" lat="39.9389700" lon="-83.8455730"/>
                int64_t nodeId = 0;
                if (!ndCurrent.attribute("id").empty())
                {
                    nodeId = ndCurrent.attribute("id").as_int64();
                    // only load nodes associated with way's that are highway's
                    auto itIdVsPlanning = nodeIdVs_isPlanningNode.find(nodeId);
                    if (itIdVsPlanning != nodeIdVs_isPlanningNode.end())
                    {
                        // don't need to add it if it is already there
                        auto itIdNode = m_idVsNode->find(nodeId);
                        if (itIdNode == m_idVsNode->end())
                        {
                            if (itIdVsPlanning->second) //it is a planning node
                            {
                                planningNodeIds.insert(nodeId);
                                planinngIndex++;
                                m_nodeIdVsPlanningIndex[nodeId] = planinngIndex;
                                m_planningIndexVsNodeId->insert(std::make_pair(planinngIndex, nodeId));
                            }

                            if (!ndCurrent.attribute("lat").empty())
                            {
                                double lat = ndCurrent.attribute("lat").as_double() * n_Const::c_Convert::dDegreesToRadians();
                                if (!ndCurrent.attribute("lon").empty())
                                {
                                    double lon = ndCurrent.attribute("lon").as_double() * n_Const::c_Convert::dDegreesToRadians();
                                    double dNorth_m(0.0);
                                    double dEast_m(0.0);
                                    auto newNode = std::unique_ptr<n_FrameworkLib::CPosition>(new n_FrameworkLib::CPosition(lat, lon, 0.0, m_flatEarth));
                                    northMax_m = (newNode->m_north_m > northMax_m) ? (newNode->m_north_m) : (northMax_m);
                                    northMin_m = (newNode->m_north_m < northMin_m) ? (newNode->m_north_m) : (northMin_m);
                                    eastMax_m = (newNode->m_east_m > eastMax_m) ? (newNode->m_east_m) : (eastMax_m);
                                    eastMin_m = (newNode->m_east_m < eastMin_m) ? (newNode->m_east_m) : (eastMin_m);
                                    m_idVsNode->insert(std::make_pair(nodeId, std::move(newNode)));
                                }
                                else //if (!ndCurrent.attribute("lon").empty())
                                {
                                    UXAS_LOG_ERROR("OSM FILE:: parse XML string failed, could not find longitude for node id[", nodeId, "]");
                                } //if (!ndCurrent.attribute("lon").empty())
                            } //if (!ndCurrent.attribute("lat").empty())
                            else
                            {
                                UXAS_LOG_ERROR("OSM FILE:: parse XML string failed, could not find longitude for node id[", nodeId, "]");
                            } //if (!ndCurrent.attribute("lat").empty())
                        } //if (itIdNode == m_idVsNode->end())
                    } //if(itIdVsPlanning != nodeIdVs_isPlanningNode.end())
                }
                else //if (!ndCurrent.attribute("id").empty())
                {
                    UXAS_LOG_ERROR("OSM FILE:: parse XML string failed, could not find node id[", nodeId, "] ");
                } //if (!ndCurrent.attribute("id").empty())
            } //ffor (pugi::xml_node ndCurrent = osmMap.child("node"); ndCurrent; ndCurrent = ndCurr ... 

            // build map of cells
            int32_t extentNorth_m = static_cast<int32_t> (std::abs(std::round(northMax_m - northMin_m)));
            int32_t extentEast_m = static_cast<int32_t> (std::abs(std::round(eastMax_m - eastMin_m)));

            if (isSuccess)
            {
                isSuccess = isProcessHighwayNodes(nodeIdVs_isPlanningNode, highWayIds);
            }
            if (isSuccess)
            {
                isSuccess = isBuildGraph(planningNodeIds, highWayIds);
            }
            if (isSuccess)
            {
                isSuccess = isBuildFullPlot(highWayIds);
            }

            // build the map of cells to nodes
            m_PositionToCellFactorNorth_m = 100;
            m_PositionToCellFactorEast_m = 100;
            //                m_PositionToCellFactorNorth_m = extentNorth_m/10;     //1 km
            //                m_PositionToCellFactorNorth_m = (extentNorth_m < 100)?(100):(extentNorth_m);   // don't go less than 100
            //                m_PositionToCellFactorEast_m = extentEast_m/10; 
            //                m_PositionToCellFactorEast_m = (extentEast_m < 100)?(100):(extentEast_m);   // don't go less than 100

            // ALL NODES
            for (auto itNode = m_idVsNode->begin(); itNode != m_idVsNode->end(); itNode++)
            {
                int32_t cellNorth_m = static_cast<int32_t> (itNode->second->m_north_m / m_PositionToCellFactorNorth_m);
                int32_t cellEast_m = static_cast<int32_t> (itNode->second->m_east_m / m_PositionToCellFactorEast_m);
                auto idCell = std::make_pair(cellNorth_m, cellEast_m);
                m_cellVsAllNodeIds.insert(std::make_pair(idCell, itNode->first));
            }
            // PLANNING NODES
            for (auto itNodeId = planningNodeIds.begin(); itNodeId != planningNodeIds.end(); itNodeId++)
            {
                auto itNode = m_idVsNode->find(*itNodeId);
                if (itNode != m_idVsNode->end())
                {
                    int32_t cellNorth_m = static_cast<int32_t> (itNode->second->m_north_m / m_PositionToCellFactorNorth_m);
                    int32_t cellEast_m = static_cast<int32_t> (itNode->second->m_east_m / m_PositionToCellFactorEast_m);
                    auto idCell = std::make_pair(cellNorth_m, cellEast_m);
                    m_cellVsPlanningNodeIds.insert(std::make_pair(idCell, *itNodeId));
                }
            }

            m_numberHighways = highWayIds.size();
            m_numberNodes = m_idVsNode->size();
            m_numberPlanningNodes = planningNodeIds.size();
            m_numberPlanningEdges = m_edges.size();

            auto endTime = std::chrono::system_clock::now();
            std::chrono::duration<double> elapsed_seconds = endTime - startTime;
            m_processMapTime_s = elapsed_seconds.count();
            UXAS_LOG_INFORM(" **** Finished reading and processing OSM File; and building the Graph: Elapsed Seconds[", m_processMapTime_s, "] ****");
            UXAS_LOG_INFORM("OSM FILE:: loaded [", m_numberHighways, "] highways, [", m_numberNodes, "] nodes, [", m_numberPlanningNodes, "] planning nodes, and [", m_numberPlanningEdges, "] planning edges");

        }
        else //if (osmMap)
        {
            UXAS_LOG_ERROR("OSM FILE:: parse XML string failed, could not find 'osm' section in osmFile[", osmFile, "] ");
        } //if (osmMap)
    } //if (result)
    else //if (osmMap)
    {
        UXAS_LOG_ERROR("OSM FILE:: parse XML string failed for osmFile[", osmFile, "]");
    }
    return (isSuccess);
}

bool OsmPlannerService::isProcessHighwayNodes(const std::unordered_map<int64_t, bool>& nodeIdVs_isPlanningNode,
                                              const std::vector<int64_t>& highWayIds)
{
    bool isSuccess(true);

    // set up the storage to lookup waypoints on planning edges based on node Id's
    for (auto itHighway = highWayIds.begin(); itHighway != highWayIds.end(); itHighway++)
    {
        // the begin node for the 'planning' edge
        auto itEdgeFirst = m_wayIdVsNodeId.end();
        auto edgeIdsForward = std::unique_ptr<s_EdgeIds>(new s_EdgeIds);
        edgeIdsForward->m_highwayId = *itHighway;
        auto edgeIdsReverse = std::unique_ptr<s_EdgeIds>(new s_EdgeIds);
        edgeIdsReverse->m_highwayId = *itHighway;

        auto itHighwayNodes = m_wayIdVsNodeId.equal_range(*itHighway);
        double distance = 0;
        n_FrameworkLib::CPosition previousNode; //used to find distance between nodes
        n_FrameworkLib::CPosition currentNode; //used to find distance between nodes
        for (auto itHighwayNode = itHighwayNodes.first; itHighwayNode != itHighwayNodes.second; itHighwayNode++)
        {
            auto itIsPlanningNode = nodeIdVs_isPlanningNode.find(itHighwayNode->second);
            if (itIsPlanningNode != nodeIdVs_isPlanningNode.end())
            {
                if (itIsPlanningNode->second)
                {
                    if (itEdgeFirst == m_wayIdVsNodeId.end())
                    {
                        previousNode = *(m_idVsNode->find(itHighwayNode->second)->second);
                        // found the start of a planning edge
                        itEdgeFirst = itHighwayNode;
                        edgeIdsForward->m_nodeIds.push_back(itHighwayNode->second);
                        edgeIdsReverse->m_nodeIds.push_front(itHighwayNode->second);
                    }
                    else
                    {
                        // found the end of a planning edge
                        //set the current node
                        currentNode = *(m_idVsNode->find(itHighwayNode->second)->second);
                        //forward
                        edgeIdsForward->m_nodeIds.push_back(itHighwayNode->second);
                        //reverse
                        edgeIdsReverse->m_nodeIds.push_front(itHighwayNode->second);
                        //add to distance 
                        distance += previousNode.relativeDistance2D_m(currentNode);
                                               
                        auto idPairForward = std::make_pair(itEdgeFirst->second, itHighwayNode->second);
                        auto itEdgeNodeIds = m_nodeIdsVsEdgeNodeIds.find(idPairForward);
                        if (itEdgeNodeIds == m_nodeIdsVsEdgeNodeIds.end())
                        {
                            // found a new edge
                            //assign distance before inserting edge
                            edgeIdsForward->m_distance_m = distance;
                            m_nodeIdsVsEdgeNodeIds.insert(std::make_pair(idPairForward, std::move(edgeIdsForward)));
                        }

                        //reverse
                        auto idPairReverse = std::make_pair(itHighwayNode->second, itEdgeFirst->second);
                        itEdgeNodeIds = m_nodeIdsVsEdgeNodeIds.find(idPairReverse);
                        if (itEdgeNodeIds == m_nodeIdsVsEdgeNodeIds.end())
                        {
                            // found a new edge
                            //assign distance before inserting edge
                            edgeIdsReverse->m_distance_m = distance;;
                            m_nodeIdsVsEdgeNodeIds.insert(std::make_pair(idPairReverse, std::move(edgeIdsReverse)));
                        }

                        // reset starting node
                        edgeIdsForward = std::unique_ptr<s_EdgeIds>(new s_EdgeIds);
                        edgeIdsForward->m_highwayId = *itHighway;
                        edgeIdsReverse = std::unique_ptr<s_EdgeIds>(new s_EdgeIds);
                        edgeIdsReverse->m_highwayId = *itHighway;

                        itEdgeFirst = itHighwayNode;
                        edgeIdsForward->m_nodeIds.push_back(itHighwayNode->second);
                        edgeIdsReverse->m_nodeIds.push_front(itHighwayNode->second);
                        
                        //reset distance and set new previousNode
                        distance = 0;
                        previousNode = *(m_idVsNode->find(itHighwayNode->second)->second);                    }
                }
                else
                {
                    if (itEdgeFirst != m_wayIdVsNodeId.end())
                    {
                        currentNode = *(m_idVsNode->find(itHighwayNode->second)->second);
                        distance += previousNode.relativeDistance2D_m(currentNode);

                        //after distance is calculated, set the previous node to the current node
                        previousNode = currentNode;
                        
                        // in the middle of a planning edge
                        edgeIdsForward->m_nodeIds.push_back(itHighwayNode->second);
                        edgeIdsReverse->m_nodeIds.push_front(itHighwayNode->second);
                    }
                }
            }
            else //if(itIsPlanningNode != nodeIdVs_isPlanningNode.end())
            {
                UXAS_LOG_ERROR("OSM FILE:: while saving highway waypoints, could not find [", itHighwayNode->second, "] in nodeIdVs_isPlanningNode.");
                isSuccess = false;
                break;
            }
        } //for(auto itHighwayNode=itHighwayNodes->first;itHighwayNode!=itHighwayNodes->second;itHighwayNode++)
    } //for(auto itHighway=highWayIds.begin();itHighway!=highWayIds.end();itHighway++)

    m_nodeIdVsSegmentBeginEndIds.clear();
    UXAS_LOG_INFORM("Calculating segment begin/end ids ... ");
    for (auto itEdgeNodeIds = m_nodeIdsVsEdgeNodeIds.begin(); itEdgeNodeIds != m_nodeIdsVsEdgeNodeIds.end(); itEdgeNodeIds++)
    {
        for (auto itNodeId = itEdgeNodeIds->second->m_nodeIds.begin(); itNodeId != itEdgeNodeIds->second->m_nodeIds.end(); itNodeId++)
        {
            m_nodeIdVsSegmentBeginEndIds.insert(std::make_pair(*itNodeId, itEdgeNodeIds->first));
        }
    }
    UXAS_LOG_INFORM("complete");

    return (isSuccess);
}

bool OsmPlannerService::isBuildFullPlot(const std::vector<int64_t>& highWayIds)
{
    bool isSuccess(true);
    if (!m_mapEdgesFileName.empty())
    {
        std::string fullPlotFile = std::string("FULLPlot_") + m_mapEdgesFileName;
        std::string plotPathFileName;
        if (uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(fullPlotFile, m_strSavePath, plotPathFileName))
        {
            std::ofstream plotStream(plotPathFileName.c_str());
            plotStream << "'node_id_1','edge_north_01','edge_east_01','edge_alt_01','node_id_2','edge_north_02','edge_east_02','edge_alt_02','edge_length_f','road_id'" << std::endl;

            for (auto itWayId = highWayIds.begin(); itWayId != highWayIds.end(); itWayId++)
            {
                auto nodeIds = m_wayIdVsNodeId.equal_range(*itWayId);
                // count nodes to put road label at center of road
                int32_t numberHighwayNodes = std::distance(nodeIds.first, nodeIds.second);
                ;
                int32_t roadLabelIndex = (numberHighwayNodes < 2) ? (0) : ((numberHighwayNodes / 2) - 1);


                int32_t countNodes(0);
                auto itLastNode(m_idVsNode->end());
                for (auto itNode = nodeIds.first; itNode != nodeIds.second; itNode++)
                {
                    int32_t roadId(0);
                    if (countNodes == roadLabelIndex)
                    {
                        roadId = *itWayId;
                    }
                    auto itStartNode = m_idVsNode->find(itNode->second);
                    if (itStartNode != m_idVsNode->end())
                    {
                        if (itLastNode != m_idVsNode->end())
                        {
                            plotStream << itLastNode->first;
                            plotStream << ",";
                            plotStream << *(itLastNode->second);
                            plotStream << ",";
                            plotStream << itStartNode->first;
                            plotStream << ",";
                            plotStream << *(itStartNode->second);
                            plotStream << ",";
                            plotStream << itStartNode->second->relativeDistance2D_m(*(itLastNode->second));
                            plotStream << ",";
                            plotStream << roadId;
                            plotStream << std::endl;
                        }
                        itLastNode = itStartNode;
                    }
                    countNodes++;
                }
            }
            plotStream.close();
            savePythonPlotCode();
        } //if(uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(m_mapEdgesFileNam ...
    }
    return (isSuccess);
}

bool OsmPlannerService::isBuildGraph(const std::unordered_set<int64_t>& planningNodeIds,
                                     const std::vector<int64_t>& highWayIds)
{
    bool isSuccess(true);

    //3) build edges

    m_edges = std::vector<n_FrameworkLib::CEdge>();
    int64_t currentWayId(-1);
    int32_t startIndex(-1);

    auto itStartId(m_idVsNode->end());

    for (auto itWayId = highWayIds.begin(); itWayId != highWayIds.end(); itWayId++)
    {
        auto nodeIds = m_wayIdVsNodeId.equal_range(*itWayId);
        double runningLength_m(0.0);
        auto itLastNode(m_idVsNode->end());
        for (auto itNode = nodeIds.first; itNode != nodeIds.second; itNode++)
        {
            auto itPlanning = planningNodeIds.find(itNode->second);
            if (itPlanning != planningNodeIds.end())
            {
                // this is a planning node
                if (*itWayId != currentWayId)
                {
                    itStartId = m_idVsNode->find(itNode->second);
                    if (itStartId != m_idVsNode->end())
                    {
                        auto itStartIndex = m_nodeIdVsPlanningIndex.find(itNode->second);
                        if (itStartIndex != m_nodeIdVsPlanningIndex.end())
                        {
                            currentWayId = *itWayId;
                            startIndex = itStartIndex->second;
                            itLastNode = itStartId;
                        }
                        else
                        {
                            currentWayId = -1; //need to find a valid start point before proceeding
                            UXAS_LOG_INFORM("OSM FILE:: while building edges:: could not find index for node[", itNode->second, "]");
                        }
                    }
                    else
                    {
                        currentWayId = -1; //need to find a valid start point before proceeding
                        UXAS_LOG_ERROR("OSM FILE:: while building edges:: could not find node[", itNode->second, "]");
                    }
                }
                else //if(itWayNodeIds->first != currentWayId)
                {
                    auto itEndId = m_idVsNode->find(itNode->second);
                    if (itEndId != m_idVsNode->end())
                    {
                        auto itEndIndex = m_nodeIdVsPlanningIndex.find(itNode->second);
                        if (itEndIndex != m_nodeIdVsPlanningIndex.end())
                        {
                            int64_t endIndex = itEndIndex->second;
                            //int64_t distance = static_cast<int64_t> (itStartId->second->relativeDistance2D_m(*(itEndId->second)));
                            int64_t distance = static_cast<int64_t> (itEndId->second->relativeDistance2D_m(*(itLastNode->second)) + runningLength_m);

                            m_edges.push_back(n_FrameworkLib::CEdge(startIndex, endIndex, distance));
                            UXAS_LOG_INFORM("startId[", itStartId->first, "] endId[", itEndId->first, "] distance[", distance, "]");

                            itStartId = itEndId;
                            itLastNode = itEndId;
                            startIndex = endIndex;

                        }
                        else
                        {
                            UXAS_LOG_ERROR("OSM FILE:: while building edges:: could not find index for node[", itNode->second, "]");
                            isSuccess = false;
                        }
                    }
                } //if(itWayNodeIds->first != currentWayId)
            }
            else //if(itPlanning != m_planningNodes.end())
            {
                auto itCurrentNode = m_idVsNode->find(itNode->second);
                if (itCurrentNode != m_idVsNode->end())
                {
                    // add length of this segment to running total
                    runningLength_m += itCurrentNode->second->relativeDistance2D_m(*(itLastNode->second));
                    itLastNode = itCurrentNode;
                }
                else
                {
                    UXAS_LOG_ERROR("OSM FILE:: while building edges:: could not find node for node ID[", itNode->second, "]");
                }
            } //if(itPlanning != m_planningNodes.end())
        }
    }

    std::vector<int32_t> edgeLengths;
    edgeLengths.reserve(m_edges.size());
    for (auto itEdge = m_edges.begin(); itEdge != m_edges.end(); itEdge++)
    {
        edgeLengths.push_back(static_cast<int32_t> (itEdge->iGetLength()));
    }

    m_graph = std::make_shared<Graph_t>(m_edges.begin(), m_edges.end(),
            edgeLengths.begin(), planningNodeIds.size());

#ifdef EUCLIDEAN_PLOT    
    if (!m_mapEdgesFileName.empty())
    {
        std::string edgesPathFileName;
        if (uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(m_mapEdgesFileName, m_strSavePath, edgesPathFileName))
        {
            std::ofstream edgesStream(edgesPathFileName.c_str());
            edgesStream << "'node_id_1','edge_north_01','edge_east_01','edge_alt_01','node_id_2','edge_north_02','edge_east_02','edge_alt_02','edge_length_f'" << std::endl;
            for (auto itEdge = m_edges.begin(); itEdge != m_edges.end(); itEdge++)
            {
                auto itNodeId_1 = m_planningIndexVsNodeId->find(itEdge->first);
                auto itNodeId_2 = m_planningIndexVsNodeId->find(itEdge->second);
                if ((itNodeId_1 != m_planningIndexVsNodeId->end()) &&
                        (itNodeId_2 != m_planningIndexVsNodeId->end()))
                {
                    auto itNode_1 = m_idVsNode->find(itNodeId_1->second);
                    auto itNode_2 = m_idVsNode->find(itNodeId_2->second);
                    if ((itNode_1 != m_idVsNode->end()) &&
                            (itNode_2 != m_idVsNode->end()))
                    {
                        edgesStream << itNodeId_1->second;
                        edgesStream << ",";
                        edgesStream << *(itNode_1->second);
                        edgesStream << ",";
                        edgesStream << itNodeId_2->second;
                        edgesStream << ",";
                        edgesStream << *(itNode_2->second);
                        edgesStream << ",";
                        edgesStream << itEdge->iGetLength();
                        edgesStream << std::endl;
                    }
                }
            }
            edgesStream.close();
        } //if(uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(m_mapEdgesFileNam ...
        savePythonPlotCode();
    } //if(!m_mapEdgesFileName.empty())
#endif  //#ifdef EUCLIDEAN_PLOT    

    return (isSuccess);
}

bool OsmPlannerService::isFindShortestRoute(const int64_t& startNodeId, const int64_t& endNodeId,
                                            int32_t& pathLength, std::deque<int64_t>& pathNodes)
{
    bool isSuccess(false);

    auto startTime = std::chrono::system_clock::now();

    auto itStartNodeIndex = m_nodeIdVsPlanningIndex.find(startNodeId);
    auto itEndNodeIndex = m_nodeIdVsPlanningIndex.find(endNodeId);
    auto itEndNode = m_idVsNode->find(endNodeId);


    if ((itStartNodeIndex != m_nodeIdVsPlanningIndex.end()) &&
            (itEndNodeIndex != m_nodeIdVsPlanningIndex.end()) &&
            (itEndNode != m_idVsNode->end()))
    {
        VertexDescriptor_t start(itStartNodeIndex->second);
        VertexDescriptor_t goal(itEndNodeIndex->second);
        std::vector<int32_t> d(num_vertices(*m_graph));

        std::vector<VertexDescriptor_t> p(num_vertices(*m_graph));
        try
        {
            // call astar named parameter interface
            boost::astar_search
                    (*m_graph, start,
                     //manhattan_distance_heuristic(m_idVsNode,m_planningIndexVsNodeId,*(itEndNode->second)),
                     euclidean_distance_heuristic(m_idVsNode, m_planningIndexVsNodeId, *(itEndNode->second)),
                     predecessor_map(boost::make_iterator_property_map(p.begin(), boost::get(boost::vertex_index, *m_graph))).
                     distance_map(boost::make_iterator_property_map(d.begin(), boost::get(boost::vertex_index, *m_graph))).
                     visitor(astar_goal_visitor(goal)));
        }
        catch (found_goal fg)
        {
            isSuccess = true; //for now :)
            // found a path to the goal
            pathLength = d[goal];
            for (VertexDescriptor_t v = goal;; v = p[v])
            {
                auto itId = m_planningIndexVsNodeId->find(static_cast<int32_t> (v));
                if (itId != m_planningIndexVsNodeId->end())
                {
                    pathNodes.push_front(itId->second);

                    if (p[v] == v)
                    {
                        break;
                    }
                }
                else
                {
                    UXAS_LOG_ERROR("OSM FILE:: while constructing shortest route from index[ ", static_cast<int64_t> (v), "], could not find corresponding node Id.");
                    isSuccess = false;
                    break;
                }
            }

            auto endTime = std::chrono::system_clock::now();
            std::chrono::duration<double> elapsed_seconds = endTime - startTime;
            m_searchTime_s = elapsed_seconds.count();
            UXAS_LOG_INFORM(" **** Finished running ASTAR search from startNodeId[", startNodeId, "] to endNodeId[", endNodeId, "] Elapsed Seconds[", elapsed_seconds.count(), "] ****");

//#define PRINT_SHORTEST_PATH
#ifdef PRINT_SHORTEST_PATH
            UXAS_LOG_INFORM("isFindShortestRoute:: Shortest path from startNodeId[", startNodeId, "] to endNodeId[", endNodeId, "] ");
            for (auto itNode = pathNodes.begin(); itNode != pathNodes.end(); itNode++)
            {
                std::cout << " -> " << *itNode;
            }
            std::cout << std::endl << "Total travel cost: [" << d[goal] << "], Number of Nodes[" << pathNodes.size() << "]" << std::endl;
#endif  //PRINT_SHORTEST_PATH
        }

    } //if((itStartNodeIndex != m_nodeIdVsPlanningIndex->end()) && ...

    if (!isSuccess)
    {
        UXAS_LOG_ERROR("Didn't find a path from startNodeId[", startNodeId, "] to endNodeId[", endNodeId, "] !");
    }


    return (isSuccess);
}

bool OsmPlannerService::isFindClosestNodeId(const n_FrameworkLib::CPosition& position,
                                            std::unordered_multimap<std::pair<int32_t, int32_t>, int64_t, PairIdHash >& cellVsNodeIds,
                                            int64_t& nodeId, double& length_m)
{
    bool isFoundNewNode(false);

    nodeId = -1;
    length_m = (std::numeric_limits<double>::max)();

    //calculate cell Id for the position
    int32_t North_m = static_cast<int32_t> (position.m_north_m) / m_PositionToCellFactorNorth_m;
    int32_t East_m = static_cast<int32_t> (position.m_east_m) / m_PositionToCellFactorEast_m;

    int32_t numberIterations(0);
    bool isFinished(false);
    while (!isFinished)
    {
        int32_t NorthMin_m = North_m - numberIterations;
        int32_t NorthMax_m = North_m + numberIterations;
        int32_t EastMin_m = East_m - numberIterations;
        int32_t EastMax_m = East_m + numberIterations;
        isFoundNewNode |= isExamineCellsInSquare(position, NorthMin_m, NorthMax_m, EastMin_m, EastMax_m, cellVsNodeIds, length_m, nodeId);
        // always check the central cell and the first square of surrounding cells
        if ((nodeId > 0) && (numberIterations > 0))
        {
            isFinished = true; // found the closest node
        }
        numberIterations++;
        if (numberIterations > 10) // 1km square
        {
            isFinished = true;
        }
    } //while(!isFinished)

    return (isFoundNewNode);
}

bool OsmPlannerService::isExamineCellsInSquare(const n_FrameworkLib::CPosition& position,
                                               const int32_t& northStart, const int32_t& northEnd,
                                               const int32_t& eastStart, const int32_t& eastEnd,
                                               std::unordered_multimap<std::pair<int32_t, int32_t>, int64_t, PairIdHash >& cellVsNodeIds,
                                               double& candidateLength_m, int64_t & candidateNodeId)
{
    bool isFoundNewNode(false);

    bool isValid = (northStart <= northEnd) && (eastStart <= eastEnd);

    if (isValid)
    {
        // south to north cells
        int32_t localNorthStart = northStart;
        while ((localNorthStart <= northEnd))
        {
            // west side of square
            isFoundNewNode |= isExamineCell(position, localNorthStart, eastStart, cellVsNodeIds, candidateLength_m, candidateNodeId);
            // east side of square
            isFoundNewNode |= isExamineCell(position, localNorthStart, eastEnd, cellVsNodeIds, candidateLength_m, candidateNodeId);
            localNorthStart += 1;
        }
        // west to east cells
        int32_t localEastStart = eastStart + 1; //already checked the corners, so add 1
        int32_t localEastEnd = eastEnd - 1; //already checked the corners, so subtract 1
        while ((localEastStart <= eastEnd))
        {
            // north side of square
            isFoundNewNode |= isExamineCell(position, northStart, localEastStart, cellVsNodeIds, candidateLength_m, candidateNodeId);
            // south side of square
            isFoundNewNode |= isExamineCell(position, northEnd, localEastStart, cellVsNodeIds, candidateLength_m, candidateNodeId);
            localEastStart += 1;
        }
    }

    return (isFoundNewNode);
}

bool OsmPlannerService::isExamineCell(const n_FrameworkLib::CPosition& position,
                                      const int32_t& north, const int32_t& east,
                                      std::unordered_multimap<std::pair<int32_t, int32_t>, int64_t, PairIdHash >& cellVsNodeIds,
                                      double& candidateLength_m, int64_t & candidateNodeId)
{
    bool isFoundNewNode(false);


    auto idCell = std::make_pair(north, east);
    auto itCell = cellVsNodeIds.equal_range(idCell);
    for (auto itNodeId = itCell.first; itNodeId != itCell.second; itNodeId++)
    {
        // - find the distance between the position and this node
        // - if it is shortest, then save the nodeId and Length        
        auto itNode = m_idVsNode->find(itNodeId->second);
        if (itNode != m_idVsNode->end())
        {
            double localLength_m = position.relativeDistance2D_m(*(itNode->second));
            if (localLength_m < candidateLength_m)
            {
                candidateLength_m = localLength_m;
                candidateNodeId = itNode->first;
                isFoundNewNode = true;
            }
        }
        else
        {
            UXAS_LOG_ERROR("isFindClosestIndices:: could not find Node based on the planning node Id[ ", itNodeId->second, "].");
            isFoundNewNode = false;
            break;
        }
    }

    return (isFoundNewNode);
}

void OsmPlannerService::findRoadIntersectionsOfCircle(const n_FrameworkLib::CPosition& center, const double& radius_m,
                                                      std::vector<n_FrameworkLib::CPosition>& intersections)
{
    intersections.clear();
    //find all of the cells inside and containing the circle
    int32_t northIdExtent = static_cast<int32_t> (center.m_north_m + radius_m) / m_PositionToCellFactorNorth_m;
    int32_t eastIdExtent = static_cast<int32_t> (center.m_east_m + radius_m) / m_PositionToCellFactorEast_m;
    int32_t southIdExtent = static_cast<int32_t> (center.m_north_m - radius_m) / m_PositionToCellFactorNorth_m;
    int32_t westIdExtent = static_cast<int32_t> (center.m_east_m - radius_m) / m_PositionToCellFactorEast_m;

    // want unique set of node iDs
    std::unordered_set<int64_t> nodeIds;

    double northId = southIdExtent;
    while ((northId <= northIdExtent))
    {
        double eastId = westIdExtent;
        while ((eastId <= eastIdExtent))
        {
            auto idCell = std::make_pair(northId, eastId);
            auto itCell = m_cellVsPlanningNodeIds.equal_range(idCell);
            if (itCell.first != m_cellVsPlanningNodeIds.end())
            {
                for (auto itNodeId = itCell.first; itNodeId != itCell.second; itNodeId++)
                {
                    nodeIds.insert(itNodeId->second);
                }
            }
            eastId += 1;
        }
        northId += 1;
    }

    // want unique set of node iDs
    std::unordered_set<int64_t> nodeIdsFinal;

    //find intersections of all highways in the extents rectangle with the circle
    // save the node, of the intersecting segment, that is furthest from the center of the circle
    for (auto itId = nodeIds.begin(); itId != nodeIds.end(); itId++)
    {
        // find all the segments with this node
        auto itSegments = m_nodeIdVsSegmentBeginEndIds.equal_range(*itId);
        if (itSegments.first != m_nodeIdVsSegmentBeginEndIds.end())
        {
            for (auto itSegment = itSegments.first; itSegment != itSegments.second; itSegment++)
            {
                auto itEdgeNodes = m_nodeIdsVsEdgeNodeIds.equal_range(itSegment->second);
                if (itEdgeNodes.first != m_nodeIdsVsEdgeNodeIds.end())
                {
                    for (auto itEdge = itEdgeNodes.first; itEdge != itEdgeNodes.second; itEdge++)
                    {
                        auto itNodeIdFirst = itEdge->second->m_nodeIds.begin();
                        auto itNodeIdSecond = itNodeIdFirst + 1;
                        for (; (itNodeIdFirst != itEdge->second->m_nodeIds.end())&&(itNodeIdSecond != itEdge->second->m_nodeIds.end());
                                itNodeIdFirst++, itNodeIdSecond++)
                        {
                            auto itNodeFirst = m_idVsNode->find(*itNodeIdFirst);
                            auto itNodeSecond = m_idVsNode->find(*itNodeIdSecond);
                            if ((itNodeFirst != m_idVsNode->end()) && (itNodeSecond != m_idVsNode->end()))
                            {
                                // check for intersection
                                double distanceFirst = center.relativeDistance2D_m(*(itNodeFirst->second));
                                double distanceSecond = center.relativeDistance2D_m(*(itNodeSecond->second));
                                if (((distanceFirst >= radius_m) && (distanceSecond <= radius_m)) ||
                                        ((distanceFirst <= radius_m) && (distanceSecond >= radius_m)))
                                {
                                    // found intersection, save the furthest node
                                    if (distanceFirst > distanceSecond)
                                    {
                                        auto itNodeId = nodeIdsFinal.find(*itNodeIdFirst);
                                        if (itNodeId == nodeIdsFinal.end())
                                        {
                                            intersections.push_back(*(itNodeFirst->second));
                                            nodeIdsFinal.insert(*itNodeIdFirst);
                                        }
                                    }
                                    else if (distanceFirst < distanceSecond)
                                    {
                                        auto itNodeId = nodeIdsFinal.find(*itNodeIdSecond);
                                        if (itNodeId == nodeIdsFinal.end())
                                        {
                                            intersections.push_back(*(itNodeSecond->second));
                                            nodeIdsFinal.insert(*itNodeIdSecond);
                                        }
                                    }
                                    else
                                    {
                                        auto itNodeId = nodeIdsFinal.find(*itNodeIdFirst);
                                        if (itNodeId == nodeIdsFinal.end())
                                        {
                                            intersections.push_back(*(itNodeFirst->second));
                                            nodeIdsFinal.insert(*itNodeIdFirst);
                                        }
                                        nodeIdsFinal.insert(*itNodeIdFirst);
                                        itNodeId = nodeIdsFinal.find(*itNodeIdSecond);
                                        if (itNodeId == nodeIdsFinal.end())
                                        {
                                            intersections.push_back(*(itNodeSecond->second));
                                            nodeIdsFinal.insert(*itNodeIdSecond);
                                        }
                                    }
                                }
                            }
                            else
                            {
                                UXAS_LOG_ERROR("OSM FILE:: findRoadIntersectionsOfCircle:: could not find node for either Id[", *itNodeIdFirst, "] or Id[", *itNodeIdSecond, "]");
                            }
                        }
                    }
                }
            }
        }
    }
}

bool OsmPlannerService::isGetNodesOnSegment(const std::pair<int64_t, int64_t>& segmentNodeIds,
                                            const int64_t& startNodeId, const int64_t& endNodeId,
                                            const bool& isAddExtraNodeIds,
                                            std::vector<int64_t>& nodeIds)
{
    bool isSuccess(false);

    auto itEdgeNodeIds = m_nodeIdsVsEdgeNodeIds.find(segmentNodeIds);
    if (itEdgeNodeIds != m_nodeIdsVsEdgeNodeIds.end())
    {
        auto edgeNodeIdLast = itEdgeNodeIds->second->m_nodeIds.begin();
        auto edgeNodeId = itEdgeNodeIds->second->m_nodeIds.begin();
        for (; edgeNodeId != itEdgeNodeIds->second->m_nodeIds.end(); edgeNodeId++)
        {
            if (!isAddExtraNodeIds)
            {
                edgeNodeIdLast = edgeNodeId;
            }
            if (((startNodeId <= 0) && (edgeNodeId == itEdgeNodeIds->second->m_nodeIds.begin())) || (*edgeNodeId == startNodeId))
            {
                nodeIds.push_back(*edgeNodeIdLast);
            }
            else if ((endNodeId > 0) && (*edgeNodeIdLast == endNodeId))
            {
                if (!nodeIds.empty())
                {
                    nodeIds.push_back(*edgeNodeIdLast);
                    if (!isAddExtraNodeIds)
                    {
                        nodeIds.push_back(*edgeNodeId);
                    }
                }
                break;
            }
            else if (!nodeIds.empty())
            {
                nodeIds.push_back(*edgeNodeIdLast);
            }
            edgeNodeIdLast = edgeNodeId;
        }
        if (isAddExtraNodeIds && !nodeIds.empty() && (edgeNodeId == itEdgeNodeIds->second->m_nodeIds.end()))
        {
            nodeIds.push_back(*edgeNodeIdLast);
        }
        isSuccess = !nodeIds.empty();
    }
    else
    {
        UXAS_LOG_ERROR("OSM FILE:: isGetNodesOnSegment:: could not find edge for node pair [", segmentNodeIds.first, ", ", segmentNodeIds.second, "]");
    }
    return (isSuccess);
}

void OsmPlannerService::savePythonPlotCode()
{
    string pythonFile = m_strSavePath + "/" + "PlotOSM_Paths.py";
    ofstream pythonFileStream(pythonFile.c_str());

    pythonFileStream << "#! /usr/bin/env python" << std::endl;
    pythonFileStream << std::endl;
    pythonFileStream << "import glob" << std::endl;
    pythonFileStream << "import matplotlib.pyplot as plt" << std::endl;
    pythonFileStream << "import matplotlib.mlab as mlab" << std::endl;
    pythonFileStream << "from matplotlib.backends.backend_pdf import PdfPages" << std::endl;
    pythonFileStream << std::endl;
    pythonFileStream << "def main():" << std::endl;
    pythonFileStream << std::endl;
    pythonFileStream << "\tfig = plt.figure(10000)" << std::endl;
    pythonFileStream << "\tfig.clf()" << std::endl;
    pythonFileStream << std::endl;
    pythonFileStream << "\t#############################################" << std::endl;
    pythonFileStream << "\t# the visible edges file" << std::endl;
    pythonFileStream << "\tPlotVisibleEdges = True" << std::endl;
    pythonFileStream << "\tif PlotVisibleEdges:" << std::endl;
    pythonFileStream << "\t\trecarrayVisibleEdges = []" << std::endl;
    pythonFileStream << "\t\tfor visibleedgesFile in glob.glob('*" << m_mapEdgesFileName << "*') :" << std::endl;
    pythonFileStream << "\t\t\tprint( 'loading [' + visibleedgesFile + ']')" << std::endl;
    pythonFileStream << "\t\t\ttry:" << std::endl;
    pythonFileStream << "\t\t\t\trecarrayVisibleEdges.append(mlab.csv2rec(visibleedgesFile))" << std::endl;
    pythonFileStream << "\t\t\texcept StandardError:" << std::endl;
    pythonFileStream << "\t\t\t\tprint( 'No edges found in [' + visibleedgesFile + ']')" << std::endl;
    pythonFileStream << "\t\t\tfor recarrayEdge in recarrayVisibleEdges :" << std::endl;
    pythonFileStream << "\t\t\t\tfor edge in recarrayEdge :" << std::endl;
    pythonFileStream << "\t\t\t\t\tline, = plt.plot([edge.edge_east_01, edge.edge_east_02], [edge.edge_north_01, edge.edge_north_02],linewidth=2.0, linestyle = '-', color = '#555555')" << std::endl;
    pythonFileStream << "\t\t\t\t\tif edge.node_id_1 < 10000:" << std::endl;
    pythonFileStream << "\t\t\t\t\t\tlabelString = '[' + str(edge.node_id_1) + ']'" << std::endl;
    pythonFileStream << "\t\t\t\t\t\tplt.text(edge.edge_east_01, edge.edge_north_01, labelString, horizontalalignment = 'left', verticalalignment = 'bottom')" << std::endl;
    pythonFileStream << "\t\t\t\t\telif edge.node_id_2 < 10000:" << std::endl;
    pythonFileStream << "\t\t\t\t\t\tlabelString = '[' + str(edge.node_id_2) + ']'" << std::endl;
    pythonFileStream << "\t\t\t\t\t\tplt.text(edge.edge_east_02, edge.edge_north_02, labelString, horizontalalignment = 'left', verticalalignment = 'bottom')" << std::endl;
    pythonFileStream << "\t\t\t\t\telif edge.road_id > 0:" << std::endl;
    pythonFileStream << "\t\t\t\t\t\tlabelString = str(edge.road_id)" << std::endl;
    pythonFileStream << "\t\t\t\t\t\tplt.text(edge.edge_east_02, edge.edge_north_02, labelString, horizontalalignment = 'left', verticalalignment = 'bottom'," << std::endl;
    pythonFileStream << "\t\t\t\t\t\t           bbox={'facecolor':'yellow', 'alpha':0.5, 'pad':0})" << std::endl;
    pythonFileStream << "\t#############################################" << std::endl;

    if (!m_shortestPathFileName.empty())
    {
        pythonFileStream << "\t# the shortest path file" << std::endl;
        pythonFileStream << "\tPlotShortestPath = True" << std::endl;
        pythonFileStream << "\tif PlotShortestPath:" << std::endl;
        pythonFileStream << "\t\trecarrayShortestPath = []" << std::endl;
        pythonFileStream << "\t\tfor ShortestPathFile in glob.glob('*" << m_shortestPathFileName << "*') :" << std::endl;
        pythonFileStream << "\t\t\tprint( 'loading [' + ShortestPathFile + ']')" << std::endl;
        pythonFileStream << "\t\t\ttry:" << std::endl;
        pythonFileStream << "\t\t\t\trecarrayShortestPath.append(mlab.csv2rec(ShortestPathFile))" << std::endl;
        pythonFileStream << "\t\t\texcept StandardError:" << std::endl;
        pythonFileStream << "\t\t\t\tprint( 'No edges found in [' + ShortestPathFile + ']')" << std::endl;
        pythonFileStream << "\t\t\tfor recarrayEdge in recarrayShortestPath :" << std::endl;
        pythonFileStream << "\t\t\t\tfor edge in recarrayEdge :" << std::endl;
        pythonFileStream << "\t\t\t\t\tline, = plt.plot([edge.edge_east_01, edge.edge_east_02], [edge.edge_north_01, edge.edge_north_02],linewidth=4.0, linestyle = '-', color = '#880000')" << std::endl;
        pythonFileStream << "\t\t\t\t\tlabelString = '[' + str(edge.node_id_1) + ']'" << std::endl;
        pythonFileStream << "\t\t\t\t\t# plt.text(edge.edge_east_01, edge.edge_north_01, labelString, horizontalalignment = 'left', verticalalignment = 'bottom')" << std::endl;
        pythonFileStream << "\t#############################################" << std::endl;
    }

    pythonFileStream << "\tprint( 'Drawing Plot')" << std::endl;
    pythonFileStream << "\tplt.title('OpenStreetMapFile[" << m_osmFileName << "]')" << std::endl;
    pythonFileStream << "\tplt.ylabel('postion north (m)')" << std::endl;
    pythonFileStream << "\tplt.xlabel('position east (m)')" << std::endl;
    pythonFileStream << "\tplt.grid(True)" << std::endl;
    pythonFileStream << "\tplt.axis('equal')" << std::endl;
    pythonFileStream << "\tplt.draw()" << std::endl;
    pythonFileStream << "\t#save a pdf file" << std::endl;
    pythonFileStream << "\tpdfFileName = 'OSM_Routes.pdf'" << std::endl;
    pythonFileStream << "\tpp = PdfPages(pdfFileName)" << std::endl;
    pythonFileStream << "\tpp.savefig()" << std::endl;
    pythonFileStream << "\tpp.close()" << std::endl;
    pythonFileStream << "\tplt.show()" << std::endl;
    pythonFileStream << std::endl;
    pythonFileStream << std::endl;
    pythonFileStream << "if __name__ == '__main__':" << std::endl;
    pythonFileStream << "    main()" << std::endl;
    pythonFileStream.close();
}







////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////

}; //namespace service
}; //namespace uxas

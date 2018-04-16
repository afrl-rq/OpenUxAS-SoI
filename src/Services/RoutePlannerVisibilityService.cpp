// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_RoutePlannerVisibility.cpp
 * Author: steve
 *
 * Created on February 19, 2015, 4:47 PM
 *
 */


#include "RoutePlannerVisibilityService.h"

#include "Position.h"   //V_POSITION_t
#include "Waypoint.h"
#include "TrajectoryParameters.h"
#include "PathInformation.h"

#include "UnitConversions.h"
#include "Constants/UxAS_String.h"

#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"

#include "afrl/cmasi/Circle.h"
#include "afrl/cmasi/Polygon.h"
#include "afrl/cmasi/Rectangle.h"

#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityConfigurationDescendants.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/EntityStateDescendants.h"

#include "pugixml.hpp"

#include <sstream>  //stringstream
#include <chrono>       // time functions

//TODO:: read in a open street map and calculate it's visibility graph



#define STRING_COMPONENT_NAME "RoutePlannerVisibility"

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_COMPONENT_TYPE "RoutePlannerVisibility"
#define STRING_XML_TASK "Task"
#define STRING_XML_TASK_TYPE "TaskType"
#define STRING_XML_TURN_RADIUS_OFFSET_M "TurnRadiusOffset_m"
#define STRING_XML_IS_ROUTE_AGGREGATOR "isRoutAggregator"
#define STRING_XML_OSM_FILE_NAME "OsmFileName"
#define STRING_XML_MINIMUM_WAYPOINT_SEPARATION_M "MinimumWaypointSeparation_m"


#define COUT_INFO_MSG(MESSAGE) std::cout << "<>RoutePlannerVisibility::" << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>RoutePlannerVisibility.:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>RoutePlannerVisibility.:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();

#define CIRCLE_BOUNDARY_INCREMENT (n_Const::c_Convert::dPiO10())

namespace uxas
{
namespace service
{
RoutePlannerVisibilityService::ServiceBase::CreationRegistrar<RoutePlannerVisibilityService>
RoutePlannerVisibilityService::s_registrar(RoutePlannerVisibilityService::s_registryServiceTypeNames());

RoutePlannerVisibilityService::RoutePlannerVisibilityService()
: ServiceBase(RoutePlannerVisibilityService::s_typeName(), RoutePlannerVisibilityService::s_directoryName())
{
};

RoutePlannerVisibilityService::~RoutePlannerVisibilityService()
{
};

bool
RoutePlannerVisibilityService::configure(const pugi::xml_node& ndComponent)

{
    bool isSucceeded{true};
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();
    //assert(strComponentType==STRING_XML_COMPONENT_TYPE)

    if (!ndComponent.attribute(STRING_XML_TURN_RADIUS_OFFSET_M).empty())
    {
        m_turnRadiusOffset_m = ndComponent.attribute(STRING_XML_TURN_RADIUS_OFFSET_M).as_double();
    }

    if (!ndComponent.attribute(STRING_XML_IS_ROUTE_AGGREGATOR).empty())
    {
        m_isRoutAggregator = ndComponent.attribute(STRING_XML_IS_ROUTE_AGGREGATOR).as_bool();
    }

    if (!ndComponent.attribute(STRING_XML_OSM_FILE_NAME).empty())
    {
        std::string osmFileName = ndComponent.attribute(STRING_XML_OSM_FILE_NAME).value();
        COUT_FILE_LINE_MSG("**** Reading and processing OSM File [" << osmFileName << "] ****");

        auto start = std::chrono::system_clock::now();

        m_osmBaseVisibilityGraph = std::make_shared<n_FrameworkLib::CVisibilityGraph>();
        auto errAddPolygon = m_osmBaseVisibilityGraph->errBuildVisibilityGraphWithOsm(osmFileName);
#ifdef STEVETEST
        if (errAddPolygon == n_FrameworkLib::CVisibilityGraph::errNoError)
        {
            errAddPolygon = m_osmBaseVisibilityGraph->errInitializeGraphBase();
            if (errAddPolygon != n_FrameworkLib::CVisibilityGraph::errNoError)
            {
                CERR_FILE_LINE_MSG("Error:: initializing base visibility graph for OSM file[" << osmFileName << "].")
            } //if(errAddPolygon == errNoError)
        }
        else //if(errAddPolygon == errNoError)
        {
            CERR_FILE_LINE_MSG("Error:: building base visibility graph for OSM file[" << osmFileName << "].")
        }
#endif  //STEVETEST
        auto end = std::chrono::system_clock::now();
        std::chrono::duration<double> elapsed_seconds = end - start;
        COUT_FILE_LINE_MSG(" **** Finished reading and processing OSM File Elapsed Seconds[" << elapsed_seconds.count() << "] ****");
    }
    if (!ndComponent.attribute(STRING_XML_MINIMUM_WAYPOINT_SEPARATION_M).empty())
    {
        m_minimumWaypointSeparation_m = ndComponent.attribute(STRING_XML_MINIMUM_WAYPOINT_SEPARATION_M).as_double();
    }

    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::OperatingRegion::Subscription);

    //ENTITY CONFIGURATIONS
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
    for(auto child : childconfigs)
        addSubscriptionAddress(child);
    
    // service 'global' path planning requests (system assumes aircraft)
    addSubscriptionAddress(uxas::messages::route::RoutePlanRequest::Subscription);
    
    // requests directed to an aircraft planner should also be handled
    addSubscriptionAddress(uxas::common::MessageGroup::AircraftPathPlanner());

    if (m_isRoutAggregator)
    {
         // ENTITY STATES
        addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
        std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
        for(auto child : childstates)
            addSubscriptionAddress(child);
        addSubscriptionAddress(uxas::messages::route::RouteRequest::Subscription);
    }

    return (isSucceeded);
}

bool
RoutePlannerVisibilityService::initialize()
{
    bool isSuccess(true);


    // need a default operating region, i.e. id=0, no boundaries
    auto operatingRegion0 = std::make_shared<afrl::cmasi::OperatingRegion>();
    operatingRegion0->setID(0);
    bProcessOperatingRegion(operatingRegion0);



    return (isSuccess);
};

bool
RoutePlannerVisibilityService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    auto entityConfig = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
    
    if (entityConfig)
    {
        auto entityConfiguration = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        m_idVsEntityConfiguration[entityConfig->getID()] = entityConfig;
        calculatePlannerParameters(entityConfig);
    }
    else if (entityState)
    {
        m_idVsEntityState[entityState->getID()] = entityState;
    }
    else if (afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
    {
        bProcessZone(std::static_pointer_cast<afrl::cmasi::AbstractZone>(receivedLmcpMessage->m_object), true);
    }
    else if (afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
    {
        bProcessZone(std::static_pointer_cast<afrl::cmasi::AbstractZone>(receivedLmcpMessage->m_object), false);
    }
    else if (afrl::cmasi::isOperatingRegion(receivedLmcpMessage->m_object.get()))
    {
        bProcessOperatingRegion(std::static_pointer_cast<afrl::cmasi::OperatingRegion>(receivedLmcpMessage->m_object));
    }
    else if (uxas::messages::route::isRouteRequest(receivedLmcpMessage->m_object.get()))
    {
        bProcessRouteRequest(std::static_pointer_cast<uxas::messages::route::RouteRequest>(receivedLmcpMessage->m_object));
    }
    else if (uxas::messages::route::isRoutePlanRequest(receivedLmcpMessage->m_object.get()))
    {
        auto request = std::static_pointer_cast<uxas::messages::route::RoutePlanRequest>(receivedLmcpMessage->m_object);
        auto itEntityConfiguration = m_idVsEntityConfiguration.find(request->getVehicleID());
        if (itEntityConfiguration != m_idVsEntityConfiguration.end() &&
                (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(itEntityConfiguration->second) ||
                std::dynamic_pointer_cast<afrl::vehicles::SurfaceVehicleConfiguration>(itEntityConfiguration->second)))
        {
            auto routePlanResponse = std::make_shared<uxas::messages::route::RoutePlanResponse>();
            if (bProcessRoutePlanRequest(request, routePlanResponse))
            {
                auto message = std::static_pointer_cast<avtas::lmcp::Object>(routePlanResponse);
                // always limited-cast route plan responses
                sendSharedLmcpObjectLimitedCastMessage(
                        getNetworkClientUnicastAddress(
                            receivedLmcpMessage->m_attributes->getSourceEntityId(),
                            receivedLmcpMessage->m_attributes->getSourceServiceId()
                        ),
                        message);
            }
            else
            {
               CERR_FILE_LINE_MSG("Error processing route plan request")
            }
        }
        else
        {
           CERR_FILE_LINE_MSG("No available air vehicle configurations")
        }
    }
    else
    {
        CERR_FILE_LINE_MSG("WARNING::Unknown Message Type Encountered receivedLmcpMessage->m_object->getLmcpTypeName()[" << receivedLmcpMessage->m_object->getLmcpTypeName() << "]")
    }
    return (false); // always false implies never terminating service from here
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////

bool RoutePlannerVisibilityService::bProcessZone(const std::shared_ptr<afrl::cmasi::AbstractZone>& abstractZone, const bool& isKeepIn)
{
    bool isSuccess(true);

    //ASSUMES:: unique Id's for all zones
    stringstream sstreamErrors;
    n_FrameworkLib::V_POSITION_t vposBoundaryPoints; //used to store the boundary points       
    isSuccess &= bFindPointsForAbstractGeometry(abstractZone->getBoundary(), vposBoundaryPoints);
    if (isSuccess)
    {
        // add new boundary to the boundary list
        m_idVsBoundary[abstractZone->getZoneID()] =
                n_FrameworkLib::PTR_BOUNDARY_t(new n_FrameworkLib::CBoundary(abstractZone->getZoneID(), isKeepIn, vposBoundaryPoints, *abstractZone));
    }

    return (isSuccess);
}

bool RoutePlannerVisibilityService::bProcessOperatingRegion(const std::shared_ptr<afrl::cmasi::OperatingRegion>& operatingRegion)
{
    bool isSuccess(true);

    //ASSUMES:: unique Id's for all zones
    //ASSUMES:: all zones used in the operating region have already been received

    //TODO:: add a unique directory to save the edges and plans built using this operating region

    auto baseVisibilityGraph = std::make_shared<n_FrameworkLib::CVisibilityGraph>();

    // check to make sure we have all of the areas for the operating region
    for (auto itArea = operatingRegion->getKeepInAreas().begin(); itArea != operatingRegion->getKeepInAreas().end(); itArea++)
    {
        auto itBoundary = m_idVsBoundary.find(*itArea);
        if (itBoundary == m_idVsBoundary.end())
        {
            CERR_FILE_LINE_MSG("ERROR:: keep in area[" << *itArea << "] not found!!!")
            isSuccess = false;
            break;
        }
        else
        {
            n_FrameworkLib::CVisibilityGraph::enError errPolygon(n_FrameworkLib::CVisibilityGraph::errNoError);
            if (!itBoundary->second->vposGetBoundaryPoints_m().empty())
            {
                errPolygon = baseVisibilityGraph->errAddPolygon(itBoundary->second->getZoneID(),
                        itBoundary->second->vposGetBoundaryPoints_m().begin(),
                        itBoundary->second->vposGetBoundaryPoints_m().end(),
                        itBoundary->second->bGetKeepInZone(),
                        itBoundary->second->getPadding()
                        );
            }
            if (errPolygon != n_FrameworkLib::CVisibilityGraph::errNoError)
            {
                CERR_FILE_LINE_MSG("ERROR::errBuildVisibilityGraphBase:: error encountered while adding Keep In Zone ID[" << itBoundary->second->getZoneID() << "] to the visibility graph.")
                isSuccess = false;
                break;
            }

        }
    }
    if (isSuccess)
    {
        for (auto itArea = operatingRegion->getKeepOutAreas().begin(); itArea != operatingRegion->getKeepOutAreas().end(); itArea++)
        {
            auto itBoundary = m_idVsBoundary.find(*itArea);
            if (itBoundary == m_idVsBoundary.end())
            {
                CERR_FILE_LINE_MSG("ERROR:: keep out area[" << *itArea << "] not found!!!")
                isSuccess = false;
                break;
            }
            else
            {
                n_FrameworkLib::CVisibilityGraph::enError errPolygon(n_FrameworkLib::CVisibilityGraph::errNoError);
                if (!itBoundary->second->vposGetBoundaryPoints_m().empty())
                {
                    errPolygon = baseVisibilityGraph->errAddPolygon(itBoundary->second->getZoneID(),
                            itBoundary->second->vposGetBoundaryPoints_m().begin(),
                            itBoundary->second->vposGetBoundaryPoints_m().end(),
                            itBoundary->second->bGetKeepInZone(),
                            itBoundary->second->getPadding()
                            );
                }
                if (errPolygon != n_FrameworkLib::CVisibilityGraph::errNoError)
                {
                    CERR_FILE_LINE_MSG("ERROR::errBuildVisibilityGraphBase:: error encountered while adding Keep Out Zone ID[" << itBoundary->second->getZoneID() << "] to the visibility graph.")
                    isSuccess = false;
                    break;
                }
            }
        }
    }
    if (isSuccess)
    {
        // initialize visibility graph
        n_FrameworkLib::CVisibilityGraph::enError errAddPolygon = baseVisibilityGraph->errFinalizePolygons();
        if (errAddPolygon == n_FrameworkLib::CVisibilityGraph::errNoError)
        {
            errAddPolygon = baseVisibilityGraph->errBuildVisibilityGraph();
            if (errAddPolygon == n_FrameworkLib::CVisibilityGraph::errNoError)
            {
                errAddPolygon = baseVisibilityGraph->errInitializeGraphBase();
                if (errAddPolygon != n_FrameworkLib::CVisibilityGraph::errNoError)
                {
                    CERR_FILE_LINE_MSG("Error:: initializing base visibility graph for OperatingRegionId[" << operatingRegion->getID() << "].")
                    isSuccess = false;
                } //if(errAddPolygon == errNoError)
            }
            else //if(errAddPolygon == n_FrameworkLib::CVisibilityGraph::errNoError)
            {
                CERR_FILE_LINE_MSG("Error:: building visibility graph for OperatingRegionId[" << operatingRegion->getID() << "].")
                isSuccess = false;
            }
        }
        else //if(errAddPolygon == n_FrameworkLib::CVisibilityGraph::errNoError)
        {
            CERR_FILE_LINE_MSG("Error:: finalizing polygon for the visibility graph for OperatingRegionId[" << operatingRegion->getID() << "].")
            isSuccess = false;
        }
    }
    if (isSuccess)
    {
        m_operatingIdVsBaseVisibilityGraph[operatingRegion->getID()] = baseVisibilityGraph;
    }

    return (isSuccess);
}

bool RoutePlannerVisibilityService::bProcessRouteRequest(const std::shared_ptr<uxas::messages::route::RouteRequest>& routeRequest)
{
    bool isSuccess(true);


    return (isSuccess);
}

bool RoutePlannerVisibilityService::bProcessRoutePlanRequest(const std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest,
        std::shared_ptr<uxas::messages::route::RoutePlanResponse>& routePlanResponse)
{
    bool isSuccess(true);

    uxas::common::utilities::CUnitConversions unitConversions;
    auto itPlannerParameters = m_idVsPlannerParameters.find(routePlanRequest->getVehicleID());
    auto itOperatingVisibilityGraph = m_operatingIdVsBaseVisibilityGraph.find(routePlanRequest->getOperatingRegion());
    if ((itPlannerParameters == m_idVsPlannerParameters.end()) ||
            ((itOperatingVisibilityGraph == m_operatingIdVsBaseVisibilityGraph.end())))
    {
        if (itPlannerParameters == m_idVsPlannerParameters.end())
        {
            CERR_FILE_LINE_MSG("Error:: could not find RouteRequest planning parameters for entity Id[" << routePlanRequest->getVehicleID() << "].")
            isSuccess = false;
        }
        if (itOperatingVisibilityGraph == m_operatingIdVsBaseVisibilityGraph.end())
        {
            CERR_FILE_LINE_MSG("Error:: could not find operating region Id[" << routePlanRequest->getOperatingRegion() << "] for RouteRequest.")
            isSuccess = false;
        }
    }
    else
    {
        routePlanResponse->setResponseID(routePlanRequest->getRequestID());
        routePlanResponse->setAssociatedTaskID(routePlanRequest->getAssociatedTaskID());
        routePlanResponse->setOperatingRegion(routePlanRequest->getOperatingRegion());
        routePlanResponse->setVehicleID(routePlanRequest->getVehicleID());

        // convert uav position and waypoint positions to lat,long
        for (auto itRequest = routePlanRequest->getRouteRequests().begin();
                itRequest != routePlanRequest->getRouteRequests().end();
                itRequest++)
        {
            auto pathInformation = std::make_shared<n_FrameworkLib::CPathInformation>();
            double dNorth_m(0.0);
            double dEast_m(0.0);

            unitConversions.ConvertLatLong_degToNorthEast_m((*itRequest)->getStartLocation()->getLatitude(),
                    (*itRequest)->getStartLocation()->getLongitude(), dNorth_m, dEast_m);
            pathInformation->posGetStart() = n_FrameworkLib::CPosition(dNorth_m, dEast_m);

            unitConversions.ConvertLatLong_degToNorthEast_m((*itRequest)->getEndLocation()->getLatitude(),
                    (*itRequest)->getEndLocation()->getLongitude(), dNorth_m, dEast_m);
            pathInformation->posGetEnd() = n_FrameworkLib::CPosition(dNorth_m, dEast_m);

            if (itOperatingVisibilityGraph->second->isFindPath(pathInformation))
            {
                auto routePlan = std::make_shared<uxas::messages::route::RoutePlan>();
                routePlan->setRouteID((*itRequest)->getRouteID());
                double routeCost_ms = static_cast<int64_t> (((itPlannerParameters->second->nominalSpeed_mps > 0.0) ?
                        (pathInformation->iGetLength() / itPlannerParameters->second->nominalSpeed_mps) : (0.0))*1000.0);
                routePlan->setRouteCost(routeCost_ms);
                if (!routePlanRequest->getIsCostOnlyRequest())
                {
                    n_FrameworkLib::CTrajectoryParameters::enPathType_t enpathType = n_FrameworkLib::CTrajectoryParameters::pathTurnStraightTurn;
                    if((!(*itRequest)->getUseEndHeading()) && (!(*itRequest)->getUseStartHeading()))
                    {
                        enpathType = n_FrameworkLib::CTrajectoryParameters::pathEuclidean;
                    }
                    
                    isCalculateWaypoints(itOperatingVisibilityGraph->second, pathInformation, routePlanRequest->getVehicleID(),
                            (*itRequest)->getStartHeading(), (*itRequest)->getEndHeading(),
                            routePlan->getWaypoints(),enpathType);
                }
                routePlanResponse->getRouteResponses().push_back(routePlan->clone());
            }
            else
            {
                CERR_FILE_LINE_MSG("Error:: could not find route for RouteRequestId[" << (*itRequest)->getRouteID() << "].")
                isSuccess = false;
            }
        }
    } //if(operatingVisibilityGraph == m_operatingIdVsBaseVisibilityGraph.end())
    return (isSuccess);
}

bool RoutePlannerVisibilityService::bFindPointsForAbstractGeometry(afrl::cmasi::AbstractGeometry* pAbstractGeometry, n_FrameworkLib::V_POSITION_t & vposBoundaryPoints)
{
    bool isSuccess(true);
    uxas::common::utilities::CUnitConversions unitConversions;

    // convert uav position and waypoint positions from lat,long
    switch (pAbstractGeometry->getLmcpType())
    {
        case afrl::cmasi::CMASIEnum::CIRCLE:
        {
            afrl::cmasi::Circle* pCircle = static_cast<afrl::cmasi::Circle*> (pAbstractGeometry);
            double dCenterNorth_m(0.0);
            double dCenterEast_m(0.0);
            unitConversions.ConvertLatLong_degToNorthEast_m(
                    pCircle->getCenterPoint()->getLatitude(),
                    pCircle->getCenterPoint()->getLongitude(),
                    dCenterNorth_m, dCenterEast_m);
            double dRadius_m = pCircle->getRadius();
            // calculate boundary points by breaking circleinto line segments
            for (double dAngle_rad = 0.0; dAngle_rad < n_Const::c_Convert::dTwoPi(); dAngle_rad += CIRCLE_BOUNDARY_INCREMENT)
            {
                double dPositionNorth_m = (dRadius_m * cos(dAngle_rad)) + dCenterNorth_m;
                double dPositionEast_m = (dRadius_m * sin(dAngle_rad)) + dCenterEast_m;
                vposBoundaryPoints.push_back(n_FrameworkLib::CPosition(dPositionNorth_m, dPositionEast_m));

            } //for(double dAngle_rad=0.0;dAngle_rad<n_Const::c_Convert::dTwoPi();dAngle_rad+=_PI_O_10)
        }
            break;
        case afrl::cmasi::CMASIEnum::POLYGON:
        {
            afrl::cmasi::Polygon* pplyBoundaryPolygon = static_cast<afrl::cmasi::Polygon*> (pAbstractGeometry);
            for (auto itPoint = pplyBoundaryPolygon->getBoundaryPoints().begin();
                    itPoint != pplyBoundaryPolygon->getBoundaryPoints().end();
                    itPoint++)
            {
                double dNorth_m(0.0);
                double dEast_m(0.0);
                unitConversions.ConvertLatLong_degToNorthEast_m((*itPoint)->getLatitude(), (*itPoint)->getLongitude(), dNorth_m, dEast_m);
                vposBoundaryPoints.push_back(n_FrameworkLib::CPosition(dNorth_m, dEast_m));
            }
        }
            break;
        case afrl::cmasi::CMASIEnum::RECTANGLE:
        {
            afrl::cmasi::Rectangle* pRectangle = static_cast<afrl::cmasi::Rectangle*> (pAbstractGeometry);
            double dCenterNorth_m(0.0);
            double dCenterEast_m(0.0);
            unitConversions.ConvertLatLong_degToNorthEast_m(
                    pRectangle->getCenterPoint()->getLatitude(),
                    pRectangle->getCenterPoint()->getLongitude(),
                    dCenterNorth_m, dCenterEast_m);
            double dRotationHeading_rad = pRectangle->getRotation() * n_Const::c_Convert::dDegreesToRadians();
            n_FrameworkLib::CWaypoint wayRotated;
            //North/East Corner
            wayRotated.m_north_m = pRectangle->getHeight() / 2.0;
            wayRotated.m_east_m = pRectangle->getWidth() / 2.0;
            wayRotated.RotateAboutOriginByHeading(dRotationHeading_rad);
            vposBoundaryPoints.push_back(n_FrameworkLib::CPosition((wayRotated.m_north_m + dCenterNorth_m), (wayRotated.m_east_m + dCenterEast_m)));

            //North/West Corner
            wayRotated.m_north_m = pRectangle->getHeight() / 2.0;
            wayRotated.m_east_m = -pRectangle->getWidth() / 2.0;
            wayRotated.RotateAboutOriginByHeading(dRotationHeading_rad);
            vposBoundaryPoints.push_back(n_FrameworkLib::CPosition((wayRotated.m_north_m + dCenterNorth_m), (wayRotated.m_east_m + dCenterEast_m)));

            //South/West Corner
            wayRotated.m_north_m = -pRectangle->getHeight() / 2.0;
            wayRotated.m_east_m = -pRectangle->getWidth() / 2.0;
            wayRotated.RotateAboutOriginByHeading(dRotationHeading_rad);
            vposBoundaryPoints.push_back(n_FrameworkLib::CPosition((wayRotated.m_north_m + dCenterNorth_m), (wayRotated.m_east_m + dCenterEast_m)));

            //South/East Corner
            wayRotated.m_north_m = -pRectangle->getHeight() / 2.0;
            wayRotated.m_east_m = pRectangle->getWidth() / 2.0;
            wayRotated.RotateAboutOriginByHeading(dRotationHeading_rad);
            vposBoundaryPoints.push_back(n_FrameworkLib::CPosition((wayRotated.m_north_m + dCenterNorth_m), (wayRotated.m_east_m + dCenterEast_m)));
        }
            break;
        default:
            CERR_FILE_LINE_MSG("ERROR::errFindPointsForAbstractGeometry:: unknown geometry type [" << pAbstractGeometry->getLmcpType() << "] encountered.")
            isSuccess = false;
            break;
    }
    return (isSuccess);
}

bool RoutePlannerVisibilityService::isCalculateWaypoints(const n_FrameworkLib::PTR_VISIBILITYGRAPH_t& visibilityGraph,
        const std::shared_ptr<n_FrameworkLib::CPathInformation>& pathInformation,
        const int64_t& vehicleId, const double& startHeading_deg, const double& endHeading_deg,
        std::vector<afrl::cmasi::Waypoint*>& planWaypoints,
        const n_FrameworkLib::CTrajectoryParameters::enPathType_t& enpathType)
{
    bool isSuccessful(true);

    auto itPlannerParameters = m_idVsPlannerParameters.find(vehicleId);
    if (itPlannerParameters != m_idVsPlannerParameters.end())
    {
        double turnRadius_m = itPlannerParameters->second->turnRadius_m;
        isSuccessful = visibilityGraph->isGenerateWaypoints(pathInformation, startHeading_deg, endHeading_deg, turnRadius_m, enpathType, m_minimumWaypointSeparation_m, planWaypoints);
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::isCalculateWaypoints:: planning parameters not found for Vehicle Id [" << vehicleId << "]!!!")
        isSuccessful = false;
    }

    return (isSuccessful);
}

void RoutePlannerVisibilityService::calculatePlannerParameters(const std::shared_ptr<afrl::cmasi::EntityConfiguration>& enityConfiguration)
{
    auto plannerParameters = std::make_shared<s_PlannerParameters>();
    if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(enityConfiguration))
    {
        auto airVehicleConfiguration = std::static_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(enityConfiguration);

        // compute turn radius for a "level turn" r = V^2/(g*tan(phi_max))
        double nominalMaxBankAngle_rad = n_Const::c_Convert::toRadians(airVehicleConfiguration->getNominalFlightProfile()->getMaxBankAngle());
        double nominalSpeed_mps = airVehicleConfiguration->getNominalSpeed();
        double dTanMaxBankAngle = tan(nominalMaxBankAngle_rad);
        double turnRadius_m = (dTanMaxBankAngle <= 0.0) ? (0.0) : (pow((nominalSpeed_mps), 2) / (n_Const::c_Convert::dGravity_mps2() * dTanMaxBankAngle));

        turnRadius_m += m_turnRadiusOffset_m;

        plannerParameters->turnRadius_m = turnRadius_m;
        plannerParameters->nominalSpeed_mps = nominalSpeed_mps;

        COUT_INFO_MSG("Vehicle Id [" << enityConfiguration->getID() << "] turnRadius_m[" << turnRadius_m << "] nominalMaxBankAngle (deg) [" << airVehicleConfiguration->getNominalFlightProfile()->getMaxBankAngle() << "] nominalSpeed_mps[" << nominalSpeed_mps << "]")
    }
    m_idVsPlannerParameters[enityConfiguration->getID()] = plannerParameters;
}



////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////

}; //namespace service
}; //namespace uxas

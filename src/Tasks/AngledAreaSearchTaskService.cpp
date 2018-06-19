// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_AngledAreaSearch.cpp
 * Author: steve
 * 
 * Created on October 19, 2015, 6:17 PM
 */


#include "AngledAreaSearchTaskService.h"

#include "Position.h"
#include "FileSystemUtilities.h"
#include "Polygon.h"

#include "afrl/cmasi/Circle.h"
#include "afrl/cmasi/Polygon.h"
#include "afrl/cmasi/Rectangle.h"
#include "uxas/messages/task/SensorFootprintResponse.h"
#include "uxas/messages/task/FootprintRequest.h"
#include "uxas/messages/task/SensorFootprintRequests.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/ROUTE.h"
#include "uxas/messages/route/RouteConstraints.h"

#include "Constants/Convert.h"

#include <sstream>      //std::stringstream
#include <iomanip>  //setfill
#include "afrl/cmasi/ServiceStatus.h"

#define STRING_XML_LANE_SPACING_MIN "SearchLaneWidthMin_m"
#define STRING_XML_LANE_SPACING_MAX "SearchLaneWidthMax_m"


namespace uxas
{
namespace service
{
namespace task
{
AngledAreaSearchTaskService::ServiceBase::CreationRegistrar<AngledAreaSearchTaskService>
AngledAreaSearchTaskService::s_registrar(AngledAreaSearchTaskService::s_registryServiceTypeNames());

AngledAreaSearchTaskService::AngledAreaSearchTaskService()
: TaskServiceBase(AngledAreaSearchTaskService::s_typeName(), AngledAreaSearchTaskService::s_directoryName()) { };

AngledAreaSearchTaskService::~AngledAreaSearchTaskService() { };

bool
AngledAreaSearchTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isAngledAreaSearchTask(m_task.get()))
        {
            m_angledAreaSearchTask = std::static_pointer_cast<afrl::impact::AngledAreaSearchTask>(m_task);
            if (m_angledAreaSearchTask)
            {
                if (m_areasOfInterest.find(m_angledAreaSearchTask->getSearchAreaID()) != m_areasOfInterest.end())
                {
                    m_areaOfInterest = m_areasOfInterest.find(m_angledAreaSearchTask->getSearchAreaID())->second;
                }
                else
                {
                    UXAS_LOG_ERROR("ERROR:: **c_Task_ImpactPointSearch::bConfigure LineOfInterest [" + std::to_string(m_angledAreaSearchTask->getSearchAreaID()) + "] was not found.");
                    isSuccessful = false;
                }
            }
            else
            {
                UXAS_LOG_ERROR("ERROR:: **AngledAreaSearchTaskService::bConfigure failed to cast a AreaSearchTask from the task pointer.");
                isSuccessful = false;
            }
        }
        else
        {
            UXAS_LOG_ERROR("ERROR:: **AngledAreaSearchTaskService::bConfigure failed: taskObject[" + m_task->getFullLmcpTypeName() + "] is not a AngledAreaSearchTask.");
            isSuccessful = false;
        }
    } //isSuccessful

      //check for taskOptions
    pugi::xml_node taskOptions = ndComponent.child(m_taskOptions_XmlTag.c_str());
    if (taskOptions)
    {
        for (pugi::xml_node ndCurrent = taskOptions.first_child(); ndCurrent; ndCurrent = ndCurrent.next_sibling())
        {
            if (std::strcmp(ndCurrent.name(), STRING_XML_LANE_SPACING_MIN) == 0)
            {
                lane_spacing_min_m = std::stoi(ndCurrent.first_child().value());
            }
            if (std::strcmp(ndCurrent.name(), STRING_XML_LANE_SPACING_MAX) == 0)
            {
                lane_spacing_max_m = std::stoi(ndCurrent.first_child().value());
            }
        }
    }

    if (lane_spacing_min_m > 0 ^ lane_spacing_max_m > 0)
    {
        UXAS_LOG_WARN("Lane spacing min and max not both positive");
    }

    addSubscriptionAddress(uxas::messages::task::SensorFootprintResponse::Subscription);
    addSubscriptionAddress(uxas::messages::route::RouteResponse::Subscription);
    return (isSuccessful);
}

/*
 * - Process and store every EntityConfiguration and EntityState message received.
 *
 * If this task is included in an AutomationRequest then:
 * 1) request sensor footprint parameters,SensorFootprintRequest, for each
 *    eligible vehicle using : GSD, view elevations, and nominal altitude
 * 2) For all sensor footprints, returned in the SensorFootprintResponse,
 *    build route constraints and send a "cost only" RoutePlanRequest.
 * 3) Construct and send TaskPlanOptions, this includes the options, an ID,
 *    and a composition string
 * 4) On receipt of a TaskImplementationRequest, construct and send a
 *    RoutePlanRequest to construct the waypoint plan for the task
 * 5) Construct, and send, TaskImplementationResponse after receiving a
 *    RouteResponse
 *
 *
 *   -AutomationRequest
 *  - GET SENSOR FOOTPRINTS
 *   -SensorFootprintRequest
 *   -SensorFootprintResponse
 *  - CONSTRUCT AN OPTION FOR EACH FOOTPRINT
 *   - RoutPlanRequest
 *   - RoutPlanResponse
 *   - TaskPlanOptions
 *  - TASK IMPLEMENTATION
 *   - TaskImplementationRequest
 *   - RouteRequest
 *   - RouteResponse
 *   - TaskImplementationResponse
 *  - VEHICLE STATE UPDATE
 *   - CameraAction (? set camera for gimble angle and FOV (ZOOM) ?)
 *   - VehicleActionCommand (? point camera ?)
 */



bool
AngledAreaSearchTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    if (uxas::messages::task::isSensorFootprintResponse(receivedLmcpObject))
    {
        if (m_idVsUniqueAutomationRequest.find(m_latestUniqueAutomationRequestId) == m_idVsUniqueAutomationRequest.end())
        {
            //TODO:: "warning received uniqueAutomationResponse[",m_latestUniqueAutomationRequestId,"] with no corresponding uniqueAutomationRequest"
        }
        else
        {
            auto currentAutomationRequest = m_idVsUniqueAutomationRequest[m_latestUniqueAutomationRequestId];
            //TODO:: need to handle multiple footprints with the same ID
            auto sensorFootprintResponse = std::static_pointer_cast<uxas::messages::task::SensorFootprintResponse>(receivedLmcpObject);
            if (sensorFootprintResponse->getResponseID() == m_task->getTaskID())
            {
                for (auto& footprint : sensorFootprintResponse->getFootprints())
                {
                    //look up options from vehicle ID
                    auto options = m_entityIDsVsTaskOptions[footprint->getFootprintResponseID()];
                    for (auto option : options)
                    {
                        auto routePlanRequest = std::make_shared<uxas::messages::route::RoutePlanRequest>();
                        routePlanRequest->setRequestID(getOptionRouteId(option));
                        routePlanRequest->setAssociatedTaskID(m_task->getTaskID());
                        routePlanRequest->setIsCostOnlyRequest(true);
                        routePlanRequest->setOperatingRegion(currentAutomationRequest->getOriginalRequest()->getOperatingRegion());
                        routePlanRequest->setVehicleID(footprint->getVehicleID());

                        auto itTaskOptionClass = m_optionIdVsTaskOptionClass.find(option);
                        if (itTaskOptionClass != m_optionIdVsTaskOptionClass.end())
                        {
                            double laneSpacing_m;

                            laneSpacing_m = footprint->getWidthCenter() * 0.9; //10% overlap

                            if (lane_spacing_max_m > 0 && lane_spacing_min_m > 0 && lane_spacing_max_m > lane_spacing_min_m)
                            {
                                //clamp
                                if (laneSpacing_m > lane_spacing_max_m)
                                {
                                    laneSpacing_m = lane_spacing_max_m;
                                }
                                else if (laneSpacing_m < lane_spacing_min_m)
                                {
                                    laneSpacing_m = lane_spacing_min_m;
                                }
                            }

                            if (laneSpacing_m > 0.01)
                            {
                                isCalculateRasterScanRoute(itTaskOptionClass->second, laneSpacing_m,
                                    footprint->getHorizontalToLeadingEdge(), footprint->getHorizontalToTrailingEdge(),
                                    routePlanRequest);
                                itTaskOptionClass->second->m_routePlanRequest = routePlanRequest;
                                m_pendingOptionRouteRequests.insert(routePlanRequest->getRequestID());
                                auto objectRouteRequest = std::static_pointer_cast<avtas::lmcp::Object>(routePlanRequest);
                                sendSharedLmcpObjectBroadcastMessage(objectRouteRequest);

                                if (!routePlanRequest->getRouteRequests().empty())
                                {
                                    auto first = routePlanRequest->getRouteRequests().front();
                                    auto last = routePlanRequest->getRouteRequests().back();
                                    itTaskOptionClass->second->m_taskOption->setStartHeading(first->getStartHeading());
                                    itTaskOptionClass->second->m_taskOption->setStartLocation(first->getStartLocation()->clone());
                                    itTaskOptionClass->second->m_taskOption->setEndHeading(last->getEndHeading());
                                    itTaskOptionClass->second->m_taskOption->setEndLocation(last->getEndLocation()->clone());
                                }
                            }
                            else
                            {
                                UXAS_LOG_ERROR("WARNING:: laneSpacing_m < 0.01 for Sensor FootPrint Id[" + std::to_string(footprint->getFootprintResponseID()) + "]");

                                auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
                                serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Error);
                                auto keyValuePair = new afrl::cmasi::KeyValuePair;
                                keyValuePair->setKey(std::string("No UniqueAutomationResponse"));
                                keyValuePair->setValue("AngledAreaSearch: Lane Spacing is Zero");
                                serviceStatus->getInfo().push_back(keyValuePair);
                                sendSharedLmcpObjectBroadcastMessage(serviceStatus);
                            }
                        }
                        else
                        {
                            UXAS_LOG_ERROR("WARNING:: Option not found for Sensor FootPrint Id[" + std::to_string(footprint->getFootprintResponseID()) + "]");
                        }
                    }
                }
            }
        }
    }
    return (false); // always false implies never terminating service from here
};

void AngledAreaSearchTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{ true };
    
    // constructs four task option for each vehicle
    
    int64_t optionId = TaskOptionClass::m_firstOptionId;
    
    std::string compositionString("+(");
    m_entityIDsVsTaskOptions.clear();
    
    auto sensorFootprintRequests = std::make_shared<uxas::messages::task::SensorFootprintRequests>();
    sensorFootprintRequests->setRequestID(m_task->getTaskID());
    for (auto itEligibleEntities = m_speedAltitudeVsEligibleEntityIdsRequested.begin(); itEligibleEntities != m_speedAltitudeVsEligibleEntityIdsRequested.end(); itEligibleEntities++)
    {
        auto elevationCurrent_rad = -60.0 * n_Const::c_Convert::dDegreesToRadians();
        auto headingCurrent_rad = n_Const::c_Convert::dNormalizeAngleRad((m_angledAreaSearchTask->getSweepAngle() * n_Const::c_Convert::dDegreesToRadians()), 0.0);
    
        for (auto entity : itEligibleEntities->second)
        {
            for (int i = 0; i < 4; i++) //four corner starting locations
            {
                std::string algebraString;
                if (isCalculateOption(entity, itEligibleEntities->first.second, itEligibleEntities->first.first,
                    headingCurrent_rad, elevationCurrent_rad, optionId, algebraString))
                {
                    //map vehicle to option
                    m_entityIDsVsTaskOptions[entity].insert(optionId);
                    compositionString += algebraString + " ";
                    optionId++;
                }
            }
    
            //make sensorFootptinRequest per vehicle
    
            // need to receive the sensor response before route request can be sent out
            // ask for footprints for each vehicle's nominal altitude, at the requested ground sample distance, and elevation angle.
            auto footprintRequest = new uxas::messages::task::FootprintRequest;
            footprintRequest->setFootprintRequestID(entity);
            footprintRequest->setVehicleID(entity);
    
            footprintRequest->getEligibleWavelengths() = m_angledAreaSearchTask->getDesiredWavelengthBands();
            footprintRequest->getElevationAngles().push_back(elevationCurrent_rad);
            sensorFootprintRequests->getFootprints().push_back(footprintRequest);
            footprintRequest = nullptr;
    }

} //for(auto itEligibleEntities=m_speedAltitudeVsEligibleEntitesRequested.begin();itEl ... 

auto objectFootprintRequests = std::static_pointer_cast<avtas::lmcp::Object>(sensorFootprintRequests);
sendSharedLmcpObjectBroadcastMessage(objectFootprintRequests);

compositionString += ")";

m_taskPlanOptions->setComposition(compositionString);

};

bool AngledAreaSearchTaskService::isCalculateOption(const int64_t& eligibleEntity,
    const double& altitude_m, const double& speed_mps,
    const double& searchAxisHeading_rad, const double& elevationLookAngle_rad,
    int64_t& optionId, std::string& algebraString)
{
    bool isSuccess(true);

    // 1) build and store new option
    // 2) add to SensorFootprintRequest

    // One Entity per option
    auto taskOption = new uxas::messages::task::TaskOption;
    taskOption->setTaskID(m_task->getTaskID());
    taskOption->setOptionID(optionId);
    //taskOption->setCost(costForward_m);
    //taskOption->setStartLocation(new afrl::cmasi::Location3D(*(routePlanForward->getWaypoints().front())));        
    //taskOption->setStartHeading(startHeading_deg);        
    //taskOption->setEndLocation(new afrl::cmasi::Location3D(*(routePlanForward->getWaypoints().back())));            
    //taskOption->setEndHeading(endHeading_deg);
    taskOption->getEligibleEntities().clear();
    taskOption->getEligibleEntities().push_back(eligibleEntity); // defaults to all entities eligible
    auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
    auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
    pTaskOptionClass->m_altitude_m = altitude_m;
    pTaskOptionClass->m_speed_mps = speed_mps;
    pTaskOptionClass->m_searchAxisHeading_rad = searchAxisHeading_rad;
    pTaskOptionClass->m_elevationLookAngle_rad = elevationLookAngle_rad;
    pTaskOptionClass->m_eligibleEntities.push_back(eligibleEntity);
    m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));

    algebraString += "p" + std::to_string(optionId) + " ";

    return (isSuccess);
};

bool AngledAreaSearchTaskService::isCalculateRasterScanRoute(std::shared_ptr<TaskOptionClass>& taskOptionClass, const double& laneSpacing_m,
    const double& sensorHorizontalToLeadingEdge_m, const double& sensorHorizontalToTrailingEdge_m,
    std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest)
{
    bool isSuccess(true);

    common::utilities::CUnitConversions unitConversions;
    auto localsearchAxisHeading_rad = n_Const::c_Convert::dNormalizeAngleRad(taskOptionClass->m_searchAxisHeading_rad, 0.0);

    std::vector<n_FrameworkLib::CPosition> searchAreaBoundary;
    auto centerPosition = std::unique_ptr<n_FrameworkLib::CPosition>();

    if (afrl::cmasi::isCircle(m_areaOfInterest->getArea()))
    {
        afrl::cmasi::Circle* pCircle = static_cast<afrl::cmasi::Circle*> (m_areaOfInterest->getArea());

        double increment_rad(n_Const::c_Convert::dPiO18());
        double theta_rad(0.0);
        centerPosition.reset(new n_FrameworkLib::CPosition(pCircle->getCenterPoint()->getLatitude() * n_Const::c_Convert::dDegreesToRadians(),
            pCircle->getCenterPoint()->getLongitude() * n_Const::c_Convert::dDegreesToRadians(), taskOptionClass->m_altitude_m, 0.0));
        while (theta_rad < n_Const::c_Convert::dTwoPi())
        {
            double currentNorth_m = pCircle->getRadius() * sin(theta_rad);
            double currentEast_m = pCircle->getRadius() * cos(theta_rad);
            n_FrameworkLib::CPosition currentPosition(currentNorth_m, currentEast_m, taskOptionClass->m_altitude_m);
            currentPosition += *centerPosition;
            searchAreaBoundary.push_back(currentPosition);
            theta_rad += increment_rad;
        }
    }
    else if (afrl::cmasi::isPolygon(m_areaOfInterest->getArea()))
    {
        //ASSUME:: convex polygon

        afrl::cmasi::Polygon* pPolygon = static_cast<afrl::cmasi::Polygon*> (m_areaOfInterest->getArea());

        // need the extents to find the center of the bounding box
        double northMax_m = (std::numeric_limits<double>::min)();
        double northMin_m = (std::numeric_limits<double>::max)();
        double eastMax_m = (std::numeric_limits<double>::min)();
        double eastMin_m = (std::numeric_limits<double>::max)();

        for (auto itpPoint = pPolygon->getBoundaryPoints().begin();
            itpPoint != pPolygon->getBoundaryPoints().end();
            itpPoint++)
        {
            n_FrameworkLib::CPosition boundaryPosition((*itpPoint)->getLatitude() * n_Const::c_Convert::dDegreesToRadians(),
                (*itpPoint)->getLongitude() * n_Const::c_Convert::dDegreesToRadians(),
                taskOptionClass->m_altitude_m, 0.0);
            searchAreaBoundary.push_back(boundaryPosition);

            if (boundaryPosition.m_north_m > northMax_m)
            {
                northMax_m = boundaryPosition.m_north_m;
            }
            if (boundaryPosition.m_north_m < northMin_m)
            {
                northMin_m = boundaryPosition.m_north_m;
            }
            if (boundaryPosition.m_east_m > eastMax_m)
            {
                eastMax_m = boundaryPosition.m_east_m;
            }
            if (boundaryPosition.m_east_m < eastMin_m)
            {
                eastMin_m = boundaryPosition.m_east_m;
            }
        } //for(std::vector<afrl::cmasi::Location2D*> itpPoint=szCountPoints<m_areaSearchTask->getSe
        double centerNorth_m = (northMax_m - northMin_m) / 2.0;
        double centerEast_m = (eastMax_m - eastMin_m) / 2.0;
        centerPosition.reset(new n_FrameworkLib::CPosition(centerNorth_m, centerEast_m, taskOptionClass->m_altitude_m));
    }
    else if (afrl::cmasi::isRectangle(m_areaOfInterest->getArea())) //if (afrl::cmasi::isCircle(m_areaSearchTask->getSearchArea()))
    {
        //case afrl::cmasi::AASTIEnum::RECTANGLE:
        afrl::cmasi::Rectangle* pRectangle = static_cast<afrl::cmasi::Rectangle*> (m_areaOfInterest->getArea());

        double centerNorth_m(0.0);
        double centerEast_m(0.0);

        unitConversions.ConvertLatLong_degToNorthEast_m(pRectangle->getCenterPoint()->getLatitude(),
            pRectangle->getCenterPoint()->getLongitude(),
            centerNorth_m, centerEast_m);
        centerPosition.reset(new n_FrameworkLib::CPosition(centerNorth_m, centerEast_m, taskOptionClass->m_altitude_m));

        double hh = pRectangle->getHeight() / 2.0;
        double hw = pRectangle->getWidth() / 2.0;

        double rot = pRectangle->getRotation() * n_Const::c_Convert::dDegreesToRadians();
        n_FrameworkLib::CPosition c(centerNorth_m, centerEast_m, taskOptionClass->m_altitude_m);

        // north/west
        auto nw = n_FrameworkLib::CPosition(centerNorth_m + (hh * cos(rot)) - (-hw * sin(rot)), centerEast_m + (hh * sin(rot)) + (-hw * cos(rot)), taskOptionClass->m_altitude_m);
        searchAreaBoundary.push_back(nw);
        // north/east
        auto ne = n_FrameworkLib::CPosition(centerNorth_m + (hh * cos(rot)) - (hw * sin(rot)), centerEast_m + (hh * sin(rot)) + (hw * cos(rot)), taskOptionClass->m_altitude_m);
        searchAreaBoundary.push_back(ne);
        // south/east
        auto se = n_FrameworkLib::CPosition(centerNorth_m + (-hh * cos(rot)) - (hw * sin(rot)), centerEast_m + (-hh * sin(rot)) + (hw * cos(rot)), taskOptionClass->m_altitude_m);
        searchAreaBoundary.push_back(se);
        // south/west
        auto sw = n_FrameworkLib::CPosition(centerNorth_m + (-hh * cos(rot)) - (-hw * sin(rot)), centerEast_m + (-hh * sin(rot)) + (-hw * cos(rot)), taskOptionClass->m_altitude_m);
        searchAreaBoundary.push_back(sw);

        localsearchAxisHeading_rad = rot; //required for certain angles (e.g. 300).
    }
    else //if (afrl::cmasi::isCircle(m_areaSearchTask->getSearchArea()))
    {
        UXAS_LOG_ERROR("isCalculateRasterScanRoute:: unknown SearchArea type encountered ["
            + m_areaOfInterest->getArea()->getFullLmcpTypeName() + "]");
        isSuccess = false;
    } //if (afrl::cmasi::isCircle(m_areaSearchTask->getSearchArea()))

    if (isSuccess)
    {
        //rotate the search area boundary, about it's center, to make adding search lanes easy
        // and
        // get the extents for search lane placement
        double northMax_m = -(std::numeric_limits<double>::max)();
        double northMin_m = (std::numeric_limits<double>::max)();
        double eastMax_m = -(std::numeric_limits<double>::max)();
        double eastMin_m = (std::numeric_limits<double>::max)();

        n_FrameworkLib::CPolygon cPolygon(taskOptionClass->m_taskOption->getOptionID());
        cPolygon.plytypGetPolygonType().bGetKeepIn() = false;
        cPolygon.dGetPolygonExpansionDistance() = 0.0;
        int64_t positionIndex = 0;
        for (auto itPoint = searchAreaBoundary.begin(); itPoint != searchAreaBoundary.end(); itPoint++, positionIndex++)
        {
            itPoint->TransformPoint2D(*centerPosition, localsearchAxisHeading_rad);
            if (itPoint->m_north_m > northMax_m)
            {
                northMax_m = itPoint->m_north_m;
            }
            if (itPoint->m_north_m < northMin_m)
            {
                northMin_m = itPoint->m_north_m;
            }
            if (itPoint->m_east_m > eastMax_m)
            {
                eastMax_m = itPoint->m_east_m;
            }
            if (itPoint->m_east_m < eastMin_m)
            {
                eastMin_m = itPoint->m_east_m;
            }
            cPolygon.viGetVerticies().push_back(positionIndex);
        }

        auto option = taskOptionClass->m_taskOption->getOptionID() % 4; //four corner options
        double currentAcrossValue_m = 0;
        double laneOver = laneSpacing_m;
        bool isUpLeg = true;

        double segmentHeadingUp_deg = localsearchAxisHeading_rad * n_Const::c_Convert::dRadiansToDegrees();
        double segmentHeadingDown_deg = n_Const::c_Convert::dNormalizeAngleDeg((segmentHeadingUp_deg + 180.0), 0.0);
        double currentSegmentHeading_deg(segmentHeadingDown_deg);

        if (option == 1 || option == 3)
        {
            currentAcrossValue_m = eastMin_m + (laneSpacing_m / 2.0);
        }
        else
        {
            currentAcrossValue_m = eastMax_m - (laneSpacing_m / 2.0);
            laneOver = -laneSpacing_m;
        }

        if (option == 3 || option == 0)
        {
            isUpLeg = false;
            currentSegmentHeading_deg = segmentHeadingUp_deg;
        }
        else
        {

        }


        if (cPolygon.errFinalizePolygon(searchAreaBoundary) == n_FrameworkLib::CPolygon::errNoError)
        {

            if (((eastMax_m - eastMin_m) * 1.1) < laneSpacing_m)
            {
                currentAcrossValue_m = eastMin_m + (eastMax_m - eastMin_m) / 2.0;
            }


            afrl::cmasi::Location3D * lastEndLocation(nullptr);
            double lastSegmentHeading_deg(segmentHeadingUp_deg);

            northMin_m -= 100000; // need to go beyond border of search area
            northMax_m += 100000;

            int64_t routeId = TaskOptionClass::m_firstImplementationRouteId;
            bool isFirstLeg = true;
            while (laneOver > 0 ? currentAcrossValue_m < eastMax_m : currentAcrossValue_m > eastMin_m)
            {
                std::vector<n_FrameworkLib::CPosition> intersectionPoints;
                cPolygon.findIntersections(searchAreaBoundary, n_FrameworkLib::CPosition(northMin_m, currentAcrossValue_m),
                    n_FrameworkLib::CPosition(northMax_m, currentAcrossValue_m), intersectionPoints);
                if (intersectionPoints.size() > 1)
                {
                    auto positionSouth = intersectionPoints.back();
                    auto positionNorth = intersectionPoints.front();
                    if (positionNorth.m_north_m < positionSouth.m_north_m)
                    {
                        positionNorth = intersectionPoints.back();
                        positionSouth = intersectionPoints.front();
                    }

                    n_FrameworkLib::CPosition startPosition;
                    n_FrameworkLib::CPosition endPosition;

                    // offset based on leading edge of sensor!!!!!
                    if (isUpLeg)
                    {
                        positionNorth.m_north_m -= sensorHorizontalToTrailingEdge_m;
                        positionSouth.m_north_m -= sensorHorizontalToLeadingEdge_m;

                        startPosition = positionSouth;
                        endPosition = positionNorth;

                        currentSegmentHeading_deg = segmentHeadingUp_deg;
                    }
                    else
                    {
                        positionNorth.m_north_m += sensorHorizontalToLeadingEdge_m;
                        positionSouth.m_north_m += sensorHorizontalToTrailingEdge_m;

                        startPosition = positionNorth;
                        endPosition = positionSouth;

                        currentSegmentHeading_deg = segmentHeadingDown_deg;
                    }
                    isUpLeg = !isUpLeg; // set up for the next (opposite direction leg)


                                        //rotate back to original frame
                    startPosition.ReTransformPoint2D(*centerPosition, localsearchAxisHeading_rad);
                    endPosition.ReTransformPoint2D(*centerPosition, localsearchAxisHeading_rad);

                    // locations
                    auto startLocation = new afrl::cmasi::Location3D();
                    double startLatitude_deg(0.0);
                    double startLongitude_deg(0.0);
                    unitConversions.ConvertNorthEast_mToLatLong_deg(startPosition.m_north_m,
                        startPosition.m_east_m,
                        startLatitude_deg, startLongitude_deg);
                    startLocation->setLatitude(startLatitude_deg);
                    startLocation->setLongitude(startLongitude_deg);
                    startLocation->setAltitude(taskOptionClass->m_altitude_m);

                    auto endLocation = new afrl::cmasi::Location3D();
                    double endLatitude_deg(0.0);
                    double endLongitude_deg(0.0);
                    unitConversions.ConvertNorthEast_mToLatLong_deg(endPosition.m_north_m,
                        endPosition.m_east_m,
                        endLatitude_deg, endLongitude_deg);
                    endLocation->setLatitude(endLatitude_deg);
                    endLocation->setLongitude(endLongitude_deg);
                    endLocation->setAltitude(taskOptionClass->m_altitude_m);

                    if (isFirstLeg) // start with a vertical path
                    {
                        // add the entrance path
                        auto routeConstraints = new uxas::messages::route::RouteConstraints;
                        routeConstraints->setRouteID(routeId);
                        routeConstraints->setStartLocation(startLocation->clone());
                        routeConstraints->setStartHeading(currentSegmentHeading_deg);
                        routeConstraints->setEndLocation(endLocation->clone());
                        routeConstraints->setEndHeading(currentSegmentHeading_deg);
                        routePlanRequest->getRouteRequests().push_back(routeConstraints);
                        routeConstraints = nullptr; //just gave up ownership
                        taskOptionClass->m_pendingRouteIds.insert(routeId);
                        routeId++;

                        isFirstLeg = false;
                        lastEndLocation = endLocation->clone();
                        lastSegmentHeading_deg = currentSegmentHeading_deg;
                        currentAcrossValue_m += laneOver;

                        continue;
                    }

                    // add a transition path (horizontal)
                    if (lastEndLocation != nullptr)
                    {
                        // add the transition to next search lane path
                        auto routeConstraints = new uxas::messages::route::RouteConstraints;
                        routeConstraints->setRouteID(routeId);
                        routeConstraints->setStartLocation(lastEndLocation);
                        lastEndLocation = nullptr;
                        routeConstraints->setStartHeading(lastSegmentHeading_deg);
                        routeConstraints->setEndLocation(startLocation->clone());
                        routeConstraints->setEndHeading(currentSegmentHeading_deg);
                        routePlanRequest->getRouteRequests().push_back(routeConstraints);
                        routeConstraints = nullptr; //just gave up ownership                                
                        taskOptionClass->m_pendingRouteIds.insert(routeId);
                        routeId++;
                    }

                    lastEndLocation = endLocation->clone();
                    lastSegmentHeading_deg = currentSegmentHeading_deg;

                    // add the vertical path
                    auto routeConstraints = new uxas::messages::route::RouteConstraints;
                    routeConstraints->setRouteID(routeId);
                    routeConstraints->setStartLocation(startLocation);
                    startLocation = nullptr;
                    routeConstraints->setStartHeading(currentSegmentHeading_deg);
                    routeConstraints->setEndLocation(endLocation);
                    endLocation = nullptr;
                    routeConstraints->setEndHeading(currentSegmentHeading_deg);
                    routeConstraints->setUseEndHeading(false);
                    routeConstraints->setUseStartHeading(false);
                    routePlanRequest->getRouteRequests().push_back(routeConstraints);
                    routeConstraints = nullptr; //just gave up ownership
                    taskOptionClass->m_pendingRouteIds.insert(routeId);
                    routeId++;

                    currentAcrossValue_m += laneOver;
                }
                else
                {
                    UXAS_LOG_ERROR("isCalculateRasterScanRoute:: a line through the boundary returned [" + std::to_string(intersectionPoints.size()) + "] intersection points.");
                    isSuccess = false;
                    break;
                }
            }
        }
        else
        {
            UXAS_LOG_ERROR("isCalculateRasterScanRoute:: error encountered while finalizing a polygon.");
            isSuccess = false;
        } //if (cPolygon.errFinalizePolygon(searchAreaBoundary) == n_FrameworkLib::CPolygon::errNoError) 
    } //if(isSuccess)
    return (isSuccess);
}


void AngledAreaSearchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{

#ifdef STEVETEST
    n_UxAS_Utilities::CUnitConversions unitConversions;
    if (m_activeDpss)
    {
        double north_m(0.0);
        double east_m(0.0);
        unitConversions.ConvertLatLong_degToNorthEast_m(entityState->getLocation()->getLatitude(),
            entityState->getLocation()->getLongitude(), north_m, east_m);
        xyPoint xyVehiclePosition(north_m, east_m, entityState->getLocation()->getAltitude());

        xyPoint xyStarePoint;
        m_activeDpss->CalculateStarePoint(xyStarePoint, xyVehiclePosition);

        /////////////////////////////////////////////////////////////////////////
        // send out new sensor steering commands for the current vehicle
        /////////////////////////////////////////////////////////////////////////

        // find the gimbal payload id to use to point the camera 
        //ASSUME: use first gimbal
        int64_t gimbalPayloadId = 0;
        auto itEntityConfiguration = m_idVsEntityConfiguration.find(entityState->getID());
        if (itEntityConfiguration != m_idVsEntityConfiguration.end())
        {
            for (auto& payload : itEntityConfiguration->second->getPayloadConfigurationList())
            {
                if (afrl::cmasi::isGimbalConfiguration(payload))
                {
                    gimbalPayloadId = payload->getPayloadID();
                    break;
                }
            }
        }

        double dLatitude_deg(0.0);
        double dLongitude_deg(0.0);
        unitConversions.ConvertNorthEast_mToLatLong_deg(xyStarePoint.x, xyStarePoint.y, dLatitude_deg, dLongitude_deg);

        //point the gimbal
        auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
        vehicleActionCommand->setVehicleID(entityState->getID());

        afrl::cmasi::GimbalStareAction* pGimbalStareAction = new afrl::cmasi::GimbalStareAction();
        pGimbalStareAction->setPayloadID(gimbalPayloadId);
        pGimbalStareAction->getAssociatedTaskList().push_back(m_task->getTaskID());
        afrl::cmasi::Location3D* stareLocation = new afrl::cmasi::Location3D;
        stareLocation->setLatitude(dLatitude_deg);
        stareLocation->setLongitude(dLongitude_deg);
        stareLocation->setAltitude(static_cast<float> (xyStarePoint.z));
        pGimbalStareAction->setStarepoint(stareLocation);
        stareLocation = nullptr;

        vehicleActionCommand->getVehicleActionList().push_back(pGimbalStareAction);
        pGimbalStareAction = nullptr;

#ifdef CONFIGURE_THE_SENSOR
        //configure the sensor
        afrl::cmasi::CameraAction* pCameraAction = new afrl::cmasi::CameraAction();
        pCameraAction->setPayloadID(pVehicle->gsdGetSettings().iGetPayloadID_Sensor());
        pCameraAction->setHorizontalFieldOfView(static_cast<float> (pVehicle->gsdGetSettings().dGetHorizantalFOV_rad() * _RAD_TO_DEG));
        pCameraAction->getAssociatedTaskList().push_back(iGetID());
        vehicleActionCommand->getVehicleActionList().push_back(pCameraAction);
        pCameraAction = 0; //don't own it
#endif  //CONFIGURE_THE_SENSOR

        // send out the response
        auto newMessage_Action = std::static_pointer_cast<avtas::lmcp::Object>(vehicleActionCommand);
        sendSharedLmcpObjectBroadcastMessage(newMessage_Action);

        //send the record video command to the axis box
        auto VideoRecord = std::make_shared<uxas::messages::uxnative::VideoRecord>();
        VideoRecord->setRecord(true);
        auto newMessage_Record = std::static_pointer_cast<avtas::lmcp::Object>(VideoRecord);
        sendSharedLmcpObjectBroadcastMessage(newMessage_Record);
    }
    else
    {
        //ERROR:: no DPSS
    }
#endif  //STEVETEST


    }


}; //namespace task
}; //namespace service
}; //namespace uxas

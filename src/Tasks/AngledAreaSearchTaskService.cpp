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
#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "uxas/messages/task/SensorFootprintResponse.h"
#include "uxas/messages/task/FootprintRequest.h"
#include "uxas/messages/task/SensorFootprintRequests.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/ROUTE.h"
#include "uxas/messages/route/RouteConstraints.h"
#include "uxas/messages/uxnative/VideoRecord.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <iomanip>  //setfill

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "AAST-AAST-AAST-AAST:: AngledAreaSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "AAST-AAST-AAST-AAST:: AngledAreaSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


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
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isAngledAreaSearchTask(m_task.get()))
        {
            m_angledAreaSearchTask = std::static_pointer_cast<afrl::impact::AngledAreaSearchTask>(m_task);
            auto foundArea = m_areasOfInterest.find(m_angledAreaSearchTask->getSearchAreaID());
            if (foundArea == m_areasOfInterest.end())
            {
                sstrErrors << "ERROR:: **c_Task_ImpactPointSearch::bConfigure AreaOfInterest [" << m_angledAreaSearchTask->getSearchAreaID() << "] was not found." << std::endl;
                CERR_FILE_LINE_MSG(sstrErrors.str())
                isSuccessful = false;
            }
            else
            {
                m_areaOfInterest = foundArea->second;
            }
        }
        else
        {
            sstrErrors << "ERROR:: **AngledAreaSearchTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a AngledAreaSearchTask." << std::endl;
            CERR_FILE_LINE_MSG(sstrErrors.str())
            isSuccessful = false;
        }
    } //isSuccessful
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
                    auto routePlanRequest = std::make_shared<uxas::messages::route::RoutePlanRequest>();
                    routePlanRequest->setRequestID(getOptionRouteId(footprint->getFootprintResponseID()));
                    routePlanRequest->setAssociatedTaskID(m_task->getTaskID());
                    routePlanRequest->setIsCostOnlyRequest(true);
                    routePlanRequest->setOperatingRegion(currentAutomationRequest->getOriginalRequest()->getOperatingRegion());
                    routePlanRequest->setVehicleID(footprint->getVehicleID());

                    auto itTaskOptionClass = m_optionIdVsTaskOptionClass.find(footprint->getFootprintResponseID());
                    if (itTaskOptionClass != m_optionIdVsTaskOptionClass.end())
                    {
                        double laneSpacing_m = footprint->getWidthCenter() * 0.9; //10% overlap
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
                                if(m_angledAreaSearchTask->getStartPoint() != nullptr)
                                {
                                    itTaskOptionClass->second->m_taskOption->setStartLocation(m_angledAreaSearchTask->getStartPoint()->clone());
                                }
                                else
                                {
                                    itTaskOptionClass->second->m_taskOption->setStartLocation(routePlanRequest->getRouteRequests().front()->getStartLocation()->clone());
                                }
                                itTaskOptionClass->second->m_taskOption->setStartHeading(routePlanRequest->getRouteRequests().front()->getStartHeading());
                                
                                itTaskOptionClass->second->m_taskOption->setEndLocation(routePlanRequest->getRouteRequests().back()->getEndLocation()->clone());
                                itTaskOptionClass->second->m_taskOption->setEndHeading(routePlanRequest->getRouteRequests().back()->getEndHeading());
                            }
                        }
                        else
                        {
                            CERR_FILE_LINE_MSG("WARNING:: laneSpacing_m < 0.01 for Sensor FootPrint Id[" << footprint->getFootprintResponseID() << "]")
                        }
                    }
                    else
                    {
                        CERR_FILE_LINE_MSG("WARNING:: Option not found for Sensor FootPrint Id[" << footprint->getFootprintResponseID() << "]")
                    }
                }
            }
        }
    }
    return (false); // always false implies never terminating service from here
};

void AngledAreaSearchTaskService::buildTaskPlanOptions()
{
    // construct a task option for each vehicle
    // note:: use only one vehicle per option

    int64_t optionId = TaskOptionClass::m_firstOptionId;

    std::string compositionString("+(");

    for (auto itEligibleEntities = m_speedAltitudeVsEligibleEntityIdsRequested.begin(); itEligibleEntities != m_speedAltitudeVsEligibleEntityIdsRequested.end(); itEligibleEntities++)
    {
        auto elevationCurrent_rad = -60.0 * n_Const::c_Convert::dDegreesToRadians();
        auto headingCurrent_rad = n_Const::c_Convert::dNormalizeAngleRad((m_angledAreaSearchTask->getSweepAngle() * n_Const::c_Convert::dDegreesToRadians()), 0.0);
        std::string algebraString;
        if (isCalculateOption(itEligibleEntities->second, itEligibleEntities->first.second, itEligibleEntities->first.first,
                              headingCurrent_rad, elevationCurrent_rad, optionId, algebraString))
        {
            compositionString += algebraString + " ";
            optionId++;
        }
    } //for(auto itEligibleEntities=m_speedAltitudeVsEligibleEntitesRequested.begin();itEl ... 

    compositionString += ")";

    m_taskPlanOptions->setComposition(compositionString);

    // send out a FootprintRequest (that will return one footprint) for each option
    auto sensorFootprintRequests = std::make_shared<uxas::messages::task::SensorFootprintRequests>();
    sensorFootprintRequests->setRequestID(m_task->getTaskID());
    for (auto itTaskOptionClass = m_optionIdVsTaskOptionClass.begin(); itTaskOptionClass != m_optionIdVsTaskOptionClass.end(); itTaskOptionClass++)
    {
        // need to receive the sensor response before route request can be sent out
        // ask for footprints for each vehicle's nominal altitude, at the requested ground sample distance, and elevation angle.
        auto footprintRequest = new uxas::messages::task::FootprintRequest;
        footprintRequest->setFootprintRequestID(itTaskOptionClass->first);
        // assume there is only one eligible entity per option
        footprintRequest->setVehicleID(itTaskOptionClass->second->m_eligibleEntities.front());
        if (m_angledAreaSearchTask->getGroundSampleDistance() > 0.0)
        {
            footprintRequest->getGroundSampleDistances().push_back(m_angledAreaSearchTask->getGroundSampleDistance());
        }
        footprintRequest->getEligibleWavelengths() = m_angledAreaSearchTask->getDesiredWavelengthBands();
        footprintRequest->getElevationAngles().push_back(itTaskOptionClass->second->m_elevationLookAngle_rad);
        sensorFootprintRequests->getFootprints().push_back(footprintRequest);
        footprintRequest = nullptr;
    }
    auto objectFootprintRequests = std::static_pointer_cast<avtas::lmcp::Object>(sensorFootprintRequests);
    sendSharedLmcpObjectBroadcastMessage(objectFootprintRequests);
};

bool AngledAreaSearchTaskService::isCalculateOption(const std::vector<int64_t>& eligibleEntities,
                                                    const double& altitude_m, const double& speed_mps,
                                                    const double& searchAxisHeading_rad, const double& elevationLookAngle_rad,
                                                    int64_t& optionId, std::string& algebraString)
{
    bool isSuccess(true);

    // 1) build and store new option
    // 2) add to SensorFootprintRequest

    for (auto itEntity = eligibleEntities.begin(); itEntity != eligibleEntities.end(); itEntity++)
    {
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
        taskOption->getEligibleEntities().push_back(*itEntity); // defaults to all entities eligible
        auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
        auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
        pTaskOptionClass->m_altitude_m = altitude_m;
        pTaskOptionClass->m_speed_mps = speed_mps;
        pTaskOptionClass->m_searchAxisHeading_rad = searchAxisHeading_rad;
        pTaskOptionClass->m_elevationLookAngle_rad = elevationLookAngle_rad;
        pTaskOptionClass->m_eligibleEntities = eligibleEntities;
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));

        algebraString += "p" + std::to_string(optionId) + " ";


        optionId++;
    }

    return (isSuccess);
};

bool AngledAreaSearchTaskService::isCalculateRasterScanRoute(std::shared_ptr<TaskOptionClass>& taskOptionClass, const double& laneSpacing_m,
                                                             const double& sensorHorizontalToLeadingEdge_m, const double& sensorHorizontalToTrailingEdge_m,
                                                             std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest)
{
    bool isSuccess(true);

    uxas::common::utilities::CUnitConversions unitConversions;
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
            else if (boundaryPosition.m_north_m < northMin_m)
            {
                northMin_m = boundaryPosition.m_north_m;
            }
            if (boundaryPosition.m_east_m > eastMax_m)
            {
                eastMax_m = boundaryPosition.m_east_m;
            }
            else if (boundaryPosition.m_east_m < eastMin_m)
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
        double northMax_m = centerNorth_m + pRectangle->getHeight() / 2.0;
        double northMin_m = centerNorth_m - pRectangle->getHeight() / 2.0;
        double eastMax_m = centerEast_m + pRectangle->getWidth() / 2.0;
        double eastMin_m = centerEast_m - pRectangle->getWidth() / 2.0;
        // north/west
        searchAreaBoundary.push_back(n_FrameworkLib::CPosition(northMax_m, eastMin_m, taskOptionClass->m_altitude_m));
        // north/east
        searchAreaBoundary.push_back(n_FrameworkLib::CPosition(northMax_m, eastMax_m, taskOptionClass->m_altitude_m));
        // south/east
        searchAreaBoundary.push_back(n_FrameworkLib::CPosition(northMin_m, eastMax_m, taskOptionClass->m_altitude_m));
        // south/west
        searchAreaBoundary.push_back(n_FrameworkLib::CPosition(northMin_m, eastMin_m, taskOptionClass->m_altitude_m));
    }
    else //if (afrl::cmasi::isCircle(m_areaSearchTask->getSearchArea()))
    {
        CERR_FILE_LINE_MSG("isCalculateRasterScanRoute:: unknown SearchArea type encountered ["
                           << m_areaOfInterest->getArea()->getFullLmcpTypeName() << "]")
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
            else if (itPoint->m_north_m < northMin_m)
            {
                northMin_m = itPoint->m_north_m;
            }
            if (itPoint->m_east_m > eastMax_m)
            {
                eastMax_m = itPoint->m_east_m;
            }
            else if (itPoint->m_east_m < eastMin_m)
            {
                eastMin_m = itPoint->m_east_m;
            }
            cPolygon.viGetVerticies().push_back(positionIndex);
        }

        if (cPolygon.errFinalizePolygon(searchAreaBoundary) == n_FrameworkLib::CPolygon::errNoError)
        {
            double currentEastValue_m = eastMin_m + (laneSpacing_m / 2.0);

            if (((eastMax_m - eastMin_m) / 2.0) < laneSpacing_m)
            {
                currentEastValue_m = eastMin_m + (eastMax_m - eastMin_m) / 2.0;
            }
            std::vector<n_FrameworkLib::CPosition> searchPoints; //rotated search points
            double segmentHeadingUp_deg = localsearchAxisHeading_rad * n_Const::c_Convert::dRadiansToDegrees();
            double segmentHeadingDown_deg = n_Const::c_Convert::dNormalizeAngleDeg((segmentHeadingUp_deg + 180.0), 0.0);
            double currentSegmentHeading_deg(segmentHeadingUp_deg);

            afrl::cmasi::Location3D * lastEndLocation(nullptr);
            double lastSegmentHeading_deg(segmentHeadingUp_deg);

            northMin_m -= 100000; // need to go beyond border of search area
            northMax_m += 100000;

            int64_t routeId = TaskOptionClass::m_firstImplementationRouteId;
            bool isFirstLeg = true;
            bool isUpLeg(true);
            while (currentEastValue_m < eastMax_m)
            {
                std::vector<n_FrameworkLib::CPosition> intersectionPoints;
                cPolygon.findIntersections(searchAreaBoundary, n_FrameworkLib::CPosition(northMin_m, currentEastValue_m),
                                           n_FrameworkLib::CPosition(northMax_m, currentEastValue_m), intersectionPoints);
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

                    if (isFirstLeg && m_angledAreaSearchTask->getStartPoint() != nullptr)
                    {
                        double dummySignalLatLon = 0;
                        n_FrameworkLib::CPosition startPoint(m_angledAreaSearchTask->getStartPoint()->getLatitude(),
                                                             m_angledAreaSearchTask->getStartPoint()->getLongitude(),
                                                             m_angledAreaSearchTask->getStartPoint()->getAltitude(), dummySignalLatLon);


                        auto startHeading_deg = (n_Const::c_Convert::dPiO2() - startPosition.relativeAngle2D_rad(startPoint)) * n_Const::c_Convert::dRadiansToDegrees();

                        // add the entrance path
                        auto routeConstraints = new uxas::messages::route::RouteConstraints;
                        routeConstraints->setRouteID(routeId);
                        routeConstraints->setStartLocation(m_angledAreaSearchTask->getStartPoint()->clone());
                        routeConstraints->setStartHeading(startHeading_deg);
                        routeConstraints->setEndLocation(startLocation->clone());
                        routeConstraints->setEndHeading(currentSegmentHeading_deg);
                        routePlanRequest->getRouteRequests().push_back(routeConstraints);
                        routeConstraints = nullptr; //just gave up ownership
                        taskOptionClass->m_pendingRouteIds.insert(routeId);
                        routeId++;
                    }

                    // add a transition path (if required)
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
                    routePlanRequest->getRouteRequests().push_back(routeConstraints);
                    routeConstraints = nullptr; //just gave up ownership
                    taskOptionClass->m_pendingRouteIds.insert(routeId);
                    routeId++;

                    isUpLeg = !isUpLeg; // set up for the next (opposite direction leg)
                    currentEastValue_m += laneSpacing_m;
                }
                else
                {
                    CERR_FILE_LINE_MSG("isCalculateRasterScanRoute:: a line through the boundary returned [" << intersectionPoints.size() << "] intersection points.")
                    isSuccess = false;
                    break;
                }
                isFirstLeg = false;
            }
        }
        else
        {
            CERR_FILE_LINE_MSG("isCalculateRasterScanRoute:: error encountered while finalizing a polygon.")
            isSuccess = false;
        } //if (cPolygon.errFinalizePolygon(searchAreaBoundary) == n_FrameworkLib::CPolygon::errNoError) 
    } //if(isSuccess)
    return (isSuccess);
}

void AngledAreaSearchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
#ifdef STEVETEST
    uxas::common::utilities::CUnitConversions unitConversions;
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

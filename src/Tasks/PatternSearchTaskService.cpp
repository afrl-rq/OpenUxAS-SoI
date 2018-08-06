// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_PatternSearch.cpp
 * Author: steve
 * 
 * Created on February 16, 2016, 6:17 PM
 */


#include "PatternSearchTaskService.h"

#include "Position.h"
#include "FileSystemUtilities.h"
#include "Polygon.h"
#include "Constants/Convert.h"

#include "afrl/cmasi/Circle.h"
#include "afrl/cmasi/Polygon.h"
#include "afrl/cmasi/Rectangle.h"
#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/VideoStreamAction.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/GimbalAngleAction.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "afrl/cmasi/CameraConfiguration.h"
#include "uxas/messages/task/SensorFootprintResponse.h"
#include "uxas/messages/task/FootprintRequest.h"
#include "uxas/messages/task/SensorFootprintRequests.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/ROUTE.h"
#include "uxas/messages/route/RouteConstraints.h"
#include "uxas/messages/uxnative/VideoRecord.h"

#include "pugixml.hpp"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <iomanip>  //setfill

#define STRING_SPIRAL_CENTER_RADIUS_M "SpiralCenterRadius_m"

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<OO>PatternSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<OO>PatternSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
PatternSearchTaskService::ServiceBase::CreationRegistrar<PatternSearchTaskService>
PatternSearchTaskService::s_registrar(PatternSearchTaskService::s_registryServiceTypeNames());

PatternSearchTaskService::PatternSearchTaskService()
: TaskServiceBase(PatternSearchTaskService::s_typeName(), PatternSearchTaskService::s_directoryName())
{
};

PatternSearchTaskService::~PatternSearchTaskService()
{
};

bool
PatternSearchTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isPatternSearchTask(m_task.get()))
        {
            m_patternSearchTask = std::static_pointer_cast<afrl::impact::PatternSearchTask>(m_task);
            if (m_patternSearchTask->getSearchLocationID() == 0)
            {
                if (m_patternSearchTask->getSearchLocation() != nullptr)
                {
                    m_patternSearchTask->setSearchLocation(m_patternSearchTask->getSearchLocation()->clone());
                }
            }
            else 
            {
                auto foundPoint = m_pointsOfInterest.find(m_patternSearchTask->getSearchLocationID());
                if (foundPoint != m_pointsOfInterest.end())
                {
                    m_pointOfInterest = foundPoint->second;
                    m_patternSearchTask->setSearchLocation(m_pointOfInterest->getLocation()->clone());
                }
                else
                {
                    sstrErrors << "ERROR:: **PatternSearchTaskService::bConfigure PointOfInterest [" << m_patternSearchTask->getSearchLocationID() << "] was not found." << std::endl;
                    CERR_FILE_LINE_MSG(sstrErrors.str())
                    isSuccessful = false;
                }
            }
            if(isSuccessful)
            {
                //////////////////////////////////////////////
                //////////// PROCESS OPTIONS /////////////////
                pugi::xml_node ndTaskOptions = ndComponent.child(m_taskOptions_XmlTag.c_str());
                if (ndTaskOptions)
                {
                    for (pugi::xml_node ndTaskOption = ndTaskOptions.first_child(); ndTaskOption; ndTaskOption = ndTaskOption.next_sibling())
                    {
                        if (std::string(STRING_SPIRAL_CENTER_RADIUS_M) == ndTaskOption.name())
                        {
                            pugi::xml_node ndOptionValue = ndTaskOption.first_child();
                            if (ndOptionValue)
                            {
                                double spiralCenterRadius_m = -1.0;
                                try
                                {
                                    spiralCenterRadius_m = std::stod(ndOptionValue.value());
                                }
                                catch (std::exception& ex)
                                {
                                    UXAS_LOG_ERROR(s_typeName(), " failed to find m_dIntruderSpeedLowerBoundFraction in [", ndOptionValue.value(), "]; EXCEPTION: ", ex.what());
                                }
                                if (spiralCenterRadius_m > 0.0)
                                {
                                    m_spiralCenterRadius_m = spiralCenterRadius_m;
                                }
                            }
                        }
                    }
                }
                
            }
            
        }
        else
        {
            sstrErrors << "ERROR:: **PatternSearchTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a PatternSearchTask." << std::endl;
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
PatternSearchTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
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
            bool isReadyToSendOptions = true;
            if (sensorFootprintResponse->getResponseID() == m_task->getTaskID())
            {
                for (auto itFootprint = sensorFootprintResponse->getFootprints().begin();
                        itFootprint != sensorFootprintResponse->getFootprints().end(); itFootprint++)
                {
                    auto routePlanRequest = std::make_shared<uxas::messages::route::RoutePlanRequest>();
                    routePlanRequest->setRequestID(getOptionRouteId((*itFootprint)->getFootprintResponseID()));
                    routePlanRequest->setAssociatedTaskID(m_task->getTaskID());
                    routePlanRequest->setIsCostOnlyRequest(true);
                    routePlanRequest->setOperatingRegion(currentAutomationRequest->getOriginalRequest()->getOperatingRegion());
                    routePlanRequest->setVehicleID((*itFootprint)->getVehicleID());

                    auto footprint = std::unique_ptr<uxas::messages::task::SensorFootprint>((*itFootprint)->clone());
                    auto itTaskOptionClass = m_optionIdVsTaskOptionClass.find(footprint->getFootprintResponseID());
                    if (itTaskOptionClass != m_optionIdVsTaskOptionClass.end())
                    {
                        itTaskOptionClass->second->m_laneSpacing_m = footprint->getWidthCenter() * 0.9; //10% overlap
                        if (itTaskOptionClass->second->m_laneSpacing_m > 0.01)
                        {
                            if (isCalculatePatternScanRoute(itTaskOptionClass->second, footprint, routePlanRequest))
                            {
                                itTaskOptionClass->second->m_routePlanRequest = routePlanRequest;
                                if (!routePlanRequest->getRouteRequests().empty())
                                {
                                    m_pendingOptionRouteRequests.insert(routePlanRequest->getRequestID());
                                    auto objectRouteRequest = std::static_pointer_cast<avtas::lmcp::Object>(routePlanRequest);
                                    sendSharedLmcpObjectBroadcastMessage(objectRouteRequest);

                                    isReadyToSendOptions = false; //need to wait to get routeresponse
                                    itTaskOptionClass->second->m_taskOption->setStartHeading(routePlanRequest->getRouteRequests().front()->getStartHeading());
                                    itTaskOptionClass->second->m_taskOption->setStartLocation(routePlanRequest->getRouteRequests().front()->getStartLocation()->clone());
                                    itTaskOptionClass->second->m_taskOption->setEndHeading(routePlanRequest->getRouteRequests().back()->getEndHeading());
                                    itTaskOptionClass->second->m_taskOption->setEndLocation(routePlanRequest->getRouteRequests().back()->getEndLocation()->clone());
                                }
                            }
                        }
                        else
                        {
                            CERR_FILE_LINE_MSG("WARNING:: m_laneSpacing_m < 0.01 for Sensor FootPrint Id[" << footprint->getFootprintResponseID() << "]")
                        }
                    }
                    else
                    {
                        CERR_FILE_LINE_MSG("WARNING:: Option not found for Sensor FootPrint Id[" << footprint->getFootprintResponseID() << "]")
                    }
                }

                if (isReadyToSendOptions)
                {
                    bool isAllOptionsComplete = true;
                    for (auto& taskOptionClass : m_optionIdVsTaskOptionClass)
                    {
                        if (!taskOptionClass.second->m_pendingRouteIds.empty())
                        {
                            isAllOptionsComplete = false;
                            break;
                        }
                    }
                    if (isAllOptionsComplete)
                    {
                        // once all options are complete, send out the message
                        auto objectTaskPlanOptions = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
                        sendSharedLmcpObjectBroadcastMessage(objectTaskPlanOptions);
                    }
                    else
                    {
                        CERR_FILE_LINE_MSG("ERROR:: Not all options were calculated for task[" << m_task->getTaskID() << "]")
                    }
                }
            } //if (sensorFootprintResponse->getResponseID() == m_task->getTaskID())
        }
    } //if (uxas::messages::task::isSensorFootprintResponse(receivedLmcpObject))
    return (false); // always false implies never terminating service from here
};

void PatternSearchTaskService::buildTaskPlanOptions()
{
    // construct a task option for each vehicle
    // note:: use only one vehicle per option

    int64_t optionId = TaskOptionClass::m_firstOptionId;

    std::string compositionString("+(");

    for (auto itEligibleEntities = m_speedAltitudeVsEligibleEntityIdsRequested.begin(); itEligibleEntities != m_speedAltitudeVsEligibleEntityIdsRequested.end(); itEligibleEntities++)
    {
        auto elevationCurrent_rad = -60.0 * n_Const::c_Convert::dDegreesToRadians();
        auto headingCurrent_rad = 0.0;
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
    for (auto itOption = m_optionIdVsTaskOptionClass.begin(); itOption != m_optionIdVsTaskOptionClass.end(); itOption++)
    {
        // need to receive the sensor response before route request can be sent out
        // ask for footprints for each vehicle's nominal altitude, at the requested ground sample distance, and elevation angle.
        auto footprintRequest = new uxas::messages::task::FootprintRequest;
        footprintRequest->setFootprintRequestID(itOption->first);
        // assume there is only one eligible entity per option
        footprintRequest->setVehicleID(itOption->second->m_eligibleEntities.front());
        if (m_patternSearchTask->getGroundSampleDistance() > 0.0)
        {
            footprintRequest->getGroundSampleDistances().push_back(m_patternSearchTask->getGroundSampleDistance());
        }
        footprintRequest->getEligibleWavelengths() = m_patternSearchTask->getDesiredWavelengthBands();
        footprintRequest->getElevationAngles().push_back(itOption->second->m_elevationLookAngle_rad);
        sensorFootprintRequests->getFootprints().push_back(footprintRequest);
        footprintRequest = nullptr;
    }
    auto objectFootprintRequests = std::static_pointer_cast<avtas::lmcp::Object>(sensorFootprintRequests);
    sendSharedLmcpObjectBroadcastMessage(objectFootprintRequests);
};

bool PatternSearchTaskService::isCalculateOption(const std::vector<int64_t>& eligibleEntities,
                                                 const double& altitude_m, const double& speed_mps,
                                                 const double& searchAxisHeading_rad, const double& elevationLookAngle_rad,
                                                 int64_t& optionId, std::string& algebraString)
{
    bool isSuccess(true);

    // 1) build and store new option
    // 2) add to SensorFootprintRequest

    for (auto& entity : eligibleEntities)
    {
        // One Entity per option, need a separate option for each vehicle due to sensor width
        auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
        pTaskOption->setTaskID(m_task->getTaskID());
        pTaskOption->setOptionID(optionId);
        pTaskOption->getEligibleEntities().clear();
        pTaskOption->getEligibleEntities().push_back(entity);
        auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
        pTaskOptionClass->m_altitude_m = altitude_m;
        pTaskOptionClass->m_speed_mps = speed_mps;
        pTaskOptionClass->m_searchAxisHeading_rad = searchAxisHeading_rad;
        pTaskOptionClass->m_elevationLookAngle_rad = elevationLookAngle_rad;
        pTaskOptionClass->m_eligibleEntities = eligibleEntities;
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));

        algebraString += "p" + std::to_string(optionId) + " ";
        optionId++;
        break;
    }
    return (isSuccess);
};

bool PatternSearchTaskService::isCalculatePatternScanRoute(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
                                                           const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint,
                                                           std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest)
{
    bool isSuccess(true);

    if (m_patternSearchTask->getPattern() == afrl::impact::AreaSearchPattern::Spiral)
    {
        m_isUseDpss = true;
        isSuccess = isCalculatePatternScanRoute_Spiral(pTaskOptionClass, sensorFootprint);
    }
    else if (m_patternSearchTask->getPattern() == afrl::impact::AreaSearchPattern::Sector)
    {
        m_isUseDpss = false;
        isSuccess = isCalculatePatternScanRoute_Sector(pTaskOptionClass, sensorFootprint, routePlanRequest);
    }
    else if (m_patternSearchTask->getPattern() == afrl::impact::AreaSearchPattern::Sweep)
    {
        m_isUseDpss = false;
        isSuccess = isCalculatePatternScanRoute_Sweep(pTaskOptionClass, sensorFootprint, routePlanRequest);
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::PatternSearchTaskService::isCalculatePatternScanRoute:: Unknown search pattern[" << m_patternSearchTask->getPattern() << "]")
        isSuccess = false;
    }

    return (isSuccess);
}

bool PatternSearchTaskService::isAddDpssSteering(std::shared_ptr<TaskOptionClass>& pTaskOptionClass, std::vector<Dpss_Data_n::xyPoint>& vxyTrueRoadPoints, std::vector<Dpss_Data_n::xyPoint>& vxyWaypoints)
{
    bool isSuccess(true);

    if ((vxyTrueRoadPoints.size() > 1) && (vxyWaypoints.size() > 1))
        {
        auto dpss = std::make_shared<Dpss>();
        std::string dpssPath = m_strSavePath + "DPSS_Output/OptionId_" + std::to_string(pTaskOptionClass->m_taskOption->getOptionID()) + "/";
        dpss->SetOutputPath(dpssPath.c_str());
        dpss->SetSingleDirectionPlanning(true);

        double azimuth{0.0};
        double elevation{n_Const::c_Convert::toRadians(-80.0)};
        double altitude{pTaskOptionClass->m_altitude_m};

        dpss->SetNominalAzimuth_rad(azimuth);
        dpss->SetNominalElevation_rad(elevation);
        dpss->SetNominalAltitude_m(altitude);

            ObjectiveParameters op; //TODO:: do I need to do anything with this?
            op.sameSide = 0;
        op.nominalAzimuthInRadians = 0.0;
        op.nominalElevationInRadians = n_Const::c_Convert::toRadians(-80.0);
            op.lreLatitudeInRadians = 0.0;
            op.lreLongitudeInRadians = 0.0;
            op.nearWaypointThresholdDistanceInMeters = 0.0;
            op.reverseManeuverDistanceInMeters = 0.0;
            op.rendezvousDistanceInMeters = 0.0;

            //1.3) Call DPSS Update Plan and Sensor Path
        dpss->SetObjective(vxyTrueRoadPoints, vxyWaypoints, &op);

        m_optionIdVsDpss.insert(std::make_pair(pTaskOptionClass->m_taskOption->getOptionID(), dpss));
                    }
    else
                    {
        // ERROR:: not enough waypoints for DPSS
        isSuccess = false;
                    }

    return (isSuccess);
            }

bool PatternSearchTaskService::isCalculatePatternScanRoute_Spiral(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
        const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint)
{
    bool isSuccess(true);

    if (pTaskOptionClass->m_laneSpacing_m > 0.0)
    {
        auto sensorSteeringSegments = std::make_shared<uxas::common::utilities::SensorSteeringSegments>();
        // SPIRAL:: r = a + b*Theta
        //psi_rad = 0*np.pi
        //laneWidth = 100
        //m_waypointSpacing_m = 50;
        //extent = 500
        //rs= []
        //thetas = []
        //theta_rad = 0.0
        //radius_m = 0
        //while radius_m <= extent:
        //    radius_m = 0.5*laneWidth * (1 + theta_rad/np.pi)
        //    rs.append(radius_m)
        //    thetas.append((theta_rad - psi_rad))
        //    print 'theta_rad[{0}], radius[{1}]'.format(theta_rad,radius_m)
        //    theta_rad = theta_rad + (m_waypointSpacing_m/radius_m)


        double northStart_m = 0.0;
        double eastStart_m = 0.0;
        m_flatEarth.ConvertLatLong_degToNorthEast_m(m_patternSearchTask->getSearchLocation()->getLatitude(),
                m_patternSearchTask->getSearchLocation()->getLongitude(), northStart_m, eastStart_m);

        auto routePlan = std::make_shared<uxas::messages::route::RoutePlan>();
        int64_t waypointNumber = 1;
        double distance_m = 0.0;
        double northLast_m = 0.0;
        double eastLast_m = 0.0;
        double theta_rad{0.0}; //could be used to set a different starting heading
        double startHeading_rad{0.0};
        double radius_m{0.0};
        bool firstPass{true};
        bool firstWaypoint{true};
        double deltaNorth_m{0.0};
        double deltaEast_m{0.0};

        int64_t roadPointIndex{0};
        std::vector<std::shared_ptr<uxas::common::utilities::SensorSteering::PointData> > waypoints;
        std::vector<std::shared_ptr<uxas::common::utilities::SensorSteering::PointData> > roadpoints;


        bool isInitialSegment{true};
        bool isSegmentEnd{false};

        double spiralBoundary_m = m_patternSearchTask->getExtent() + (0.55 * pTaskOptionClass->m_laneSpacing_m);
        while (radius_m <= spiralBoundary_m)
        {
            radius_m = 0.45 * pTaskOptionClass->m_laneSpacing_m * (1.0 + theta_rad / n_Const::c_Convert::dPi());
            if (firstPass)
            {
                radius_m = 50.0;
            }
            double north_m = (radius_m * sin(theta_rad - startHeading_rad)) + northStart_m;
            double east_m = (radius_m * cos(theta_rad - startHeading_rad)) + eastStart_m;

            roadpoints.push_back(std::make_shared<uxas::common::utilities::SensorSteering::PointData>(roadPointIndex, north_m, east_m));

            double vehicleRadius_m = radius_m;
            if (vehicleRadius_m < m_spiralCenterRadius_m)
            {
                vehicleRadius_m = m_spiralCenterRadius_m;
            }
            else if (isInitialSegment)
            {
                isInitialSegment = false;
                isSegmentEnd = true;
            }
            double vehicleNorth_m = (vehicleRadius_m * sin(theta_rad - startHeading_rad)) + northStart_m;
            double vehicleEast_m = (vehicleRadius_m * cos(theta_rad - startHeading_rad)) + eastStart_m;
            deltaNorth_m = vehicleNorth_m - northLast_m;
            deltaEast_m = vehicleEast_m - eastLast_m;
            double latitude_deg(0.0);
            double longitude_deg(0.0);
            m_flatEarth.ConvertNorthEast_mToLatLong_deg(vehicleNorth_m, vehicleEast_m,
                                                            latitude_deg, longitude_deg);
            auto waypoint = new afrl::cmasi::Waypoint();
            waypoint->setNumber(waypointNumber);
            waypoint->setLatitude(latitude_deg);
            waypoint->setLongitude(longitude_deg);
            waypoint->setAltitude(pTaskOptionClass->m_altitude_m);
            waypoint->setSpeed(pTaskOptionClass->m_speed_mps);
            waypoints.push_back(std::make_shared<uxas::common::utilities::SensorSteering::PointData>(waypoint->getNumber(), waypoint, m_flatEarth));
            routePlan->getWaypoints().push_back(waypoint);
            if (firstWaypoint)
            {
                pTaskOptionClass->m_taskOption->setStartLocation(new afrl::cmasi::Location3D(*(waypoint)));
                pTaskOptionClass->m_taskOption->setStartHeading(n_Const::c_Convert::toDegrees(startHeading_rad));
                firstWaypoint = false;
            }
            waypoint = nullptr; // gave up ownership

            if (isSegmentEnd)
            {
                sensorSteeringSegments->AddSegment(waypoints, roadpoints);
                auto lastWaypoint = std::make_shared<uxas::common::utilities::SensorSteering::PointData>(*(waypoints.back()));;
                auto lastRoadpoint = std::make_shared<uxas::common::utilities::SensorSteering::PointData>(*(roadpoints.back()));
                waypoints.clear();
                roadpoints.clear();
                waypoints.push_back(lastWaypoint);
                roadpoints.push_back(lastRoadpoint);
                isSegmentEnd = false;;
            }

            roadPointIndex++;
            waypointNumber++; // next waypoint
            distance_m += pow((pow(deltaNorth_m, 2.0) + pow(deltaEast_m, 2.0)), 0.5);

            if (radius_m > 0.0) // divide by zero check
            {
                assert(m_waypointSpacing_m > 0.0);
                theta_rad += m_waypointSpacing_m / radius_m; // set the next theta based on the desired waypoint separation
            }
            northLast_m = vehicleNorth_m;
            eastLast_m = vehicleEast_m;
            firstPass = false;
        }
        if (!waypoints.empty() && !roadpoints.empty())
            {
            sensorSteeringSegments->AddSegment(waypoints, roadpoints);
            waypoints.clear();
            roadpoints.clear();
        }

        double endHeading_deg = n_Const::c_Convert::toDegrees(atan2(deltaEast_m, deltaNorth_m));
        pTaskOptionClass->m_taskOption->setEndLocation(new afrl::cmasi::Location3D(*(routePlan->getWaypoints().back())));
        pTaskOptionClass->m_taskOption->setEndHeading(endHeading_deg);

        int64_t routeId = TaskOptionClass::m_firstImplementationRouteId;
        routePlan->setRouteID(routeId);

        double cost_ms = static_cast<int64_t> (((pTaskOptionClass->m_speed_mps > 0.0) ? (distance_m / pTaskOptionClass->m_speed_mps) : (0.0))*1000.0);
        routePlan->setRouteCost(cost_ms);

        pTaskOptionClass->m_orderedRouteIdVsPlan[routePlan->getRouteID()] = routePlan;

        pTaskOptionClass->m_taskOption->setCost(cost_ms);

        m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());
        m_optionIdVsSensorSteeringSegments.insert(std::make_pair(pTaskOptionClass->m_taskOption->getOptionID(), sensorSteeringSegments));
    }
    else //if(pTaskOptionClass->m_laneSpacing_m > 0.0)
    {
        //ERROR:: m_laneSpacing_m must be > 0.0
        isSuccess = false;
    }
    return (isSuccess);
}

bool PatternSearchTaskService::isCalculatePatternScanRoute_Sector(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
                                                                  const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint,
                                                                  std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest)
{
    bool isSuccess(true);

    double northStart_m = 0.0;
    double eastStart_m = 0.0;
    m_flatEarth.ConvertLatLong_degToNorthEast_m(m_patternSearchTask->getSearchLocation()->getLatitude(),
                                                    m_patternSearchTask->getSearchLocation()->getLongitude(), northStart_m, eastStart_m);

    std::vector<std::shared_ptr < s_SearchLeg>> searchSegments;
    double arcStep_rad = pTaskOptionClass->m_laneSpacing_m / m_patternSearchTask->getExtent();
    bool isUpLeg = true;
    double theta_rad = 0.0;
    double stopTheta_rad = n_Const::c_Convert::dPi() - (arcStep_rad / 2.0);
    while (theta_rad < stopTheta_rad)
    {
        double radius1Offset_m = sensorFootprint->getHorizontalToLeadingEdge();
        double radius2Offset_m = sensorFootprint->getHorizontalToTrailingEdge();
        if (!isUpLeg)
        {
            radius1Offset_m = -sensorFootprint->getHorizontalToTrailingEdge();
            radius2Offset_m = -sensorFootprint->getHorizontalToLeadingEdge();
        }
        double radius1_m = m_patternSearchTask->getExtent() + radius1Offset_m;
        double radius2_m = m_patternSearchTask->getExtent() - radius2Offset_m;
        double north1_m = northStart_m - (radius1_m * sin(theta_rad));
        double east1_m = eastStart_m - (radius1_m * cos(theta_rad));
        n_FrameworkLib::CPosition position1(north1_m, east1_m);

        double north2_m = northStart_m + (radius2_m * sin(theta_rad));
        double east2_m = eastStart_m + (radius2_m * cos(theta_rad));
        n_FrameworkLib::CPosition position2(north2_m, east2_m);
        if (isUpLeg)
        {
            double heading_deg = n_Const::c_Convert::dNormalizeAngleDeg((n_Const::c_Convert::dPi() + n_Const::c_Convert::dPiO2() - position1.relativeAngle2D_rad(position2)) * n_Const::c_Convert::dRadiansToDegrees(), 0.0);
            searchSegments.push_back(
                                     std::make_shared<s_SearchLeg>(position1, position2, heading_deg));
        }
        else
        {
            double heading_deg = n_Const::c_Convert::dNormalizeAngleDeg((n_Const::c_Convert::dPi() + n_Const::c_Convert::dPiO2() - position2.relativeAngle2D_rad(position1)) * n_Const::c_Convert::dRadiansToDegrees(), 0.0);
            searchSegments.push_back(
                                     std::make_shared<s_SearchLeg>(position2, position1, heading_deg));
        }

        isUpLeg = !isUpLeg; // set up for the next (opposite direction leg)
        theta_rad += arcStep_rad;
    }

    int64_t routeId = TaskOptionClass::m_firstImplementationRouteId;
    afrl::cmasi::Location3D * lastEndLocation(nullptr);
    double lastSegmentHeading_deg(0.0);
    double currentSegmentHeading_deg(0.0);

    for (auto& searchSegment : searchSegments)
    {
        currentSegmentHeading_deg = searchSegment->m_heading_deg;
        // locations
        auto startLocation = new afrl::cmasi::Location3D();
        double startLatitude_deg(0.0);
        double startLongitude_deg(0.0);
        m_flatEarth.ConvertNorthEast_mToLatLong_deg(searchSegment->m_startPosition.m_north_m,
                                                        searchSegment->m_startPosition.m_east_m, startLatitude_deg, startLongitude_deg);
        startLocation->setLatitude(startLatitude_deg);
        startLocation->setLongitude(startLongitude_deg);
        startLocation->setAltitude(pTaskOptionClass->m_altitude_m);

        auto endLocation = new afrl::cmasi::Location3D();
        double endLatitude_deg(0.0);
        double endLongitude_deg(0.0);
        m_flatEarth.ConvertNorthEast_mToLatLong_deg(searchSegment->m_endPosition.m_north_m,
                                                        searchSegment->m_endPosition.m_east_m, endLatitude_deg, endLongitude_deg);
        endLocation->setLatitude(endLatitude_deg);
        endLocation->setLongitude(endLongitude_deg);
        endLocation->setAltitude(pTaskOptionClass->m_altitude_m);

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
            pTaskOptionClass->m_pendingRouteIds.insert(routeId);
            routeId++;
        }

        lastEndLocation = endLocation->clone();
        lastSegmentHeading_deg = currentSegmentHeading_deg;

        // add the search path
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
        pTaskOptionClass->m_pendingRouteIds.insert(routeId);
        routeId++;

    } //for(auto& searchSegment : searchSegments)
    return (isSuccess);
}

bool PatternSearchTaskService::isCalculatePatternScanRoute_Sweep(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
                                                                 const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint,
                                                                 std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest)
{
    bool isSuccess(true);

    double northStart_m = 0.0;
    double eastStart_m = 0.0;
    m_flatEarth.ConvertLatLong_degToNorthEast_m(m_patternSearchTask->getSearchLocation()->getLatitude(),
                                                    m_patternSearchTask->getSearchLocation()->getLongitude(), northStart_m, eastStart_m);

    return (isSuccess);
}

bool PatternSearchTaskService::isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse, std::shared_ptr<TaskOptionClass>& taskOptionClass,
        int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route)
{

    auto sensorSteeringSegments = m_optionIdVsSensorSteeringSegments.find(taskOptionClass->m_taskOption->getOptionID());
    if (sensorSteeringSegments != m_optionIdVsSensorSteeringSegments.end())
    {
        m_activeSensorSteeringSegments = sensorSteeringSegments->second;
    }
    return (false); // want the base class to build the response
}

void PatternSearchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    if (m_activeSensorSteeringSegments)
    {
        auto itOptionWaypointId = m_optionWaypointIdVsFinalWaypointId.find(entityState->getCurrentWaypoint());
        if (itOptionWaypointId != m_optionWaypointIdVsFinalWaypointId.end())
        {
            auto optionWaypointId = itOptionWaypointId->second;
            afrl::cmasi::Location3D sensorStarePoint;
            m_activeSensorSteeringSegments->FindSensorStarePoint(optionWaypointId, entityState->getLocation(), sensorStarePoint, m_flatEarth);

            /////////////////////////////////////////////////////////////////////////
            // Send VideoStreamAction if specified in this RoadSearchTask
            /////////////////////////////////////////////////////////////////////////
            if (!m_isVideoStreamActionSent)
            {
                //COUT_MSG("Test if the message has been sent" << m_roadSearchTask->getTaskID()) // DWCTest
                m_isVideoStreamActionSent = true;
                if (!m_patternSearchTask->getDesiredWavelengthBands().empty()) // If task has a specified desired wavelength
                {
                    //COUT_MSG("DesiredWavelength is not empty") // DWCTest
                    // Assume if desiredWavelengthBands is not empty, then there is only 1 specified wavelength
                    auto itEntityConfiguration = m_entityConfigurations.find(entityState->getID());
                    if (itEntityConfiguration != m_entityConfigurations.end())
                    {
                        //COUT_MSG("itEntityConfiguration if statement") // DWCTest
                        // Search through this RoadSearchTask's active entity's payloads
                        for (auto& payload : itEntityConfiguration->second->getPayloadConfigurationList())
                        {
                            // check if this payload is a camera
                            //COUT_FILE_LINE_MSG("Loop through payloads") // DWCTest
                            if (afrl::cmasi::isCameraConfiguration(payload))
                            {
                                //COUT_FILE_LINE_MSG("CameraConfiguration") // DWCTest
                                // is this camera the desired type (wavelength)
                                auto cameraConfiguration = static_cast<afrl::cmasi::CameraConfiguration*> (payload);
                                if (cameraConfiguration->getSupportedWavelengthBand() == m_patternSearchTask->getDesiredWavelengthBands().front())
                                {
                                    auto videoStreamAction = std::make_shared<afrl::cmasi::VideoStreamAction>();
                                    videoStreamAction->setVideoStreamID(0); // 0 is default value
                                    videoStreamAction->setActiveSensor(cameraConfiguration->getPayloadID()); // find the camera id
                                    // TODO - store current cameraid ...
                                    sendSharedLmcpObjectBroadcastMessage(videoStreamAction);
                                    //COUT_FILE_LINE_MSG("POINT:: Latitude[" << avstate->getLocation()->getLatitude() << "] Longitude[" << avstate->getLocation()->getLongitude() << "]")
                                    //COUT_FILE_LINE_MSG("Sending VehicleStreamAction") // DWCTest
                                    break;
                                }
                            }
                        }
                    }

                }
            }
            /////////////////////////////////////////////////////////////////////////
            // send out new sensor steering commands for the current vehicle
            /////////////////////////////////////////////////////////////////////////

            // find the gimbal payload id to use to point the camera 
            //ASSUME: use first gimbal
            int64_t gimbalPayloadId = 0;
            auto itEntityConfiguration = m_entityConfigurations.find(entityState->getID());
            if (itEntityConfiguration != m_entityConfigurations.end())
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

            //point the gimbal
            auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
            vehicleActionCommand->setVehicleID(entityState->getID());

            afrl::cmasi::GimbalStareAction* pGimbalStareAction = new afrl::cmasi::GimbalStareAction();
            pGimbalStareAction->setPayloadID(gimbalPayloadId);
            pGimbalStareAction->getAssociatedTaskList().push_back(m_patternSearchTask->getTaskID());
            pGimbalStareAction->setStarepoint(sensorStarePoint.clone());
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
            sendSharedLmcpObjectBroadcastMessage(VideoRecord);
        }
        else    //if(itOptionWaypointId != m_optionWaypointIdVsFinalWaypointId.end())
        {
            UXAS_LOG_ERROR("PatternSearchTaskService::activeEntityState::", " Can not point sensor. Option waypoint ID for waypoint number [" , entityState->getCurrentWaypoint() , "] not found.");
        }
        }
    else //if(m_isUseDpss)
        {
        /////////////////////////////////////////////////////////////////////////
        // send out new sensor steering commands for the current vehicle
        /////////////////////////////////////////////////////////////////////////

        // find the gimbal payload id to use to point the camera 
        //ASSUME: use first gimbal
        int64_t gimbalPayloadId = 0;
        auto itEntityConfiguration = m_entityConfigurations.find(entityState->getID());
        if (itEntityConfiguration != m_entityConfigurations.end())
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

        //point the gimbal
        auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
        vehicleActionCommand->setVehicleID(entityState->getID());

        auto gimbalAngleAction = new afrl::cmasi::GimbalAngleAction();
        gimbalAngleAction->setPayloadID(gimbalPayloadId);
        gimbalAngleAction->getAssociatedTaskList().push_back(m_patternSearchTask->getTaskID());
        gimbalAngleAction->setAzimuth(0.0);
        gimbalAngleAction->setElevation(-80.0);

        vehicleActionCommand->getVehicleActionList().push_back(gimbalAngleAction);
        gimbalAngleAction = nullptr;

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
    } ////if(m_isUseDpss)
}
}; //namespace task
}; //namespace service
}; //namespace uxas

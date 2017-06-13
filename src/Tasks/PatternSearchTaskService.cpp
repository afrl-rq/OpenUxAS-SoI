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

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "PTNST-PTNST-PTNST-PTNST:: PatternSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "PTNST-PTNST-PTNST-PTNST:: PatternSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
PatternSearchTaskService::ServiceBase::CreationRegistrar<PatternSearchTaskService>
PatternSearchTaskService::s_registrar(PatternSearchTaskService::s_registryServiceTypeNames());

PatternSearchTaskService::PatternSearchTaskService()
: TaskServiceBase(PatternSearchTaskService::s_typeName(), PatternSearchTaskService::s_directoryName()) { };

PatternSearchTaskService::~PatternSearchTaskService() { };

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
            if (m_patternSearchTask)
            {
				if (m_patternSearchTask->getSearchLocationID() == 0)
				{
					if (m_patternSearchTask->getSearchLocation() != nullptr)
					{
						m_patternSearchTask->setSearchLocation(m_patternSearchTask->getSearchLocation()->clone());
					}
				}
				else 
                {
                    if ((m_pointOfInterest) && (m_patternSearchTask->getSearchLocationID() == m_pointOfInterest->getPointID()))
                    {
                        m_patternSearchTask->setSearchLocation(m_pointOfInterest->getLocation()->clone());
                    }
                    else
                    {
                        sstrErrors << "ERROR:: **PatternSearchTaskService::bConfigure PointOfInterest [" << m_patternSearchTask->getSearchLocationID() << "] was not found." << std::endl;
                        CERR_FILE_LINE_MSG(sstrErrors.str())
                        isSuccessful = false;
                    }
                }
            }
            else
            {
                sstrErrors << "ERROR:: **PatternSearchTaskService::bConfigure failed to cast a AreaSearchTask from the task pointer." << std::endl;
                CERR_FILE_LINE_MSG(sstrErrors.str())
                isSuccessful = false;
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

    int64_t optionId = 1;

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
        m_isUseDpss = false;
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

bool PatternSearchTaskService::isCalculatePatternScanRoute_Spiral(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
                                                                  const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint)
{
    bool isSuccess(true);

    uxas::common::utilities::CUnitConversions unitConversions;
    double northStart_m = 0.0;
    double eastStart_m = 0.0;
    unitConversions.ConvertLatLong_degToNorthEast_m(m_patternSearchTask->getSearchLocation()->getLatitude(),
                                                    m_patternSearchTask->getSearchLocation()->getLongitude(), northStart_m, eastStart_m);

    if (m_isUseDpss)
    {
        std::vector<Dpss_Data_n::xyPoint> vxyTrueRoad;
        std::vector<Dpss_Data_n::xyPoint> vxyTrueWaypoints;

        bool firstPass = true;
        uint32_t pointId(1); // road point Id's for DPSS
        double startHeading_rad = 1.5 * n_Const::c_Convert::dPi();
        double theta_rad = 0.0; //could be used to set a different starting heading
        double radius_m = 0.0;
        while (radius_m <= m_patternSearchTask->getExtent())
        {
            radius_m = 0.5 * pTaskOptionClass->m_laneSpacing_m * (1.0 + theta_rad / n_Const::c_Convert::dPi());
            double north_m = (radius_m * sin(theta_rad - startHeading_rad)) + northStart_m;
            double east_m = (radius_m * cos(theta_rad - startHeading_rad)) + eastStart_m;
            if (firstPass)
            {
                // add a starting point that puts the leading edge of the sensor on the start of the spiral
                north_m -= sensorFootprint->getHorizontalToLeadingEdge() * cos(startHeading_rad);
                east_m -= sensorFootprint->getHorizontalToLeadingEdge() * sin(startHeading_rad);
                Dpss_Data_n::xyPoint xyTemp(north_m, east_m, pTaskOptionClass->m_altitude_m);
                xyTemp.id = pointId;
                vxyTrueRoad.push_back(xyTemp);
                pointId++;
            }
            Dpss_Data_n::xyPoint xyTemp(north_m, east_m, pTaskOptionClass->m_altitude_m);
            xyTemp.id = pointId;
            vxyTrueRoad.push_back(xyTemp);
            pointId++;

            if (radius_m > 0.0) // divide by zero check
            {
                assert(m_waypointSpacing_m > 0.0);
                theta_rad += m_waypointSpacing_m / radius_m; // set the next theta based on the desired waypoint separation
            }
            firstPass = false;
        }

        vxyTrueWaypoints = vxyTrueRoad;

        int32_t maxNumberWaypointsPoints = static_cast<int32_t> (vxyTrueRoad.size());

        // first reset the Dpss
        auto dpss = std::make_shared<Dpss>();
        std::string dpssPath = m_strSavePath + "DPSS_Output/OptionId_" + std::to_string(pTaskOptionClass->m_taskOption->getOptionID()) + "/";
        dpss->SetOutputPath(dpssPath.c_str());
        dpss->SetSingleDirectionPlanning(false);

        //1.1) Call DPSS Plan the path (quickly)
        dpss->PreProcessPath(vxyTrueWaypoints);

        // need non-const versions of these 
        auto localAzimuthLookAngle_rad = 0.0;
        auto localElevationLookAngle_rad = -60.0 * n_Const::c_Convert::dDegreesToRadians();
        auto localNominalAltitude_m = pTaskOptionClass->m_altitude_m;

        dpss->SetNominalAzimuth_rad(localAzimuthLookAngle_rad);
        dpss->SetNominalElevation_rad(localElevationLookAngle_rad);
        dpss->SetNominalAltitude_m(localNominalAltitude_m);

        dpss->PlanQuickly(vxyTrueWaypoints, maxNumberWaypointsPoints);

        //1.2) Offset the Path in Forward and reverse directions

        //1.2.1) Call DPSS Offset Path Forward
        std::vector<Dpss_Data_n::xyPoint> vxyPlanForward;
        dpss->OffsetPlanForward(vxyTrueWaypoints, vxyPlanForward);

        //1.2.2) Call DPSS Offset Path Reverse
        std::vector<Dpss_Data_n::xyPoint> vxyPlanReverse;
        dpss->OffsetPlanReverse(vxyTrueWaypoints, vxyPlanReverse);

        if ((vxyPlanForward.size() > 1) && (vxyPlanReverse.size() > 1))
        {
            std::vector<Dpss_Data_n::xyPoint> vxyPlanComplete;
            vxyPlanComplete = vxyPlanForward;
            vxyPlanComplete.insert(vxyPlanComplete.end(), vxyPlanReverse.begin(), vxyPlanReverse.end());


            ObjectiveParameters op; //TODO:: do I need to do anything with this?
            op.sameSide = 0;
            op.nominalAzimuthInRadians = localAzimuthLookAngle_rad;
            op.nominalElevationInRadians = localElevationLookAngle_rad;
            op.lreLatitudeInRadians = 0.0;
            op.lreLongitudeInRadians = 0.0;
            op.nearWaypointThresholdDistanceInMeters = 0.0;
            op.reverseManeuverDistanceInMeters = 0.0;
            op.rendezvousDistanceInMeters = 0.0;

            //1.3) Call DPSS Update Plan and Sensor Path
            dpss->SetObjective(vxyTrueRoad, vxyPlanComplete, &op);


            // build the forward waypoints && calculate cost
            auto routePlan = std::make_shared<uxas::messages::route::RoutePlan>();
            int64_t waypointNumber = 1;
            auto itWaypoint = vxyPlanForward.begin();
            auto itWaypointlast = vxyPlanForward.begin();
            double distance_m = 0.0;
            double startHeading_deg = 0.0;
            double endHeading_deg = 0.0;
            for (; itWaypoint != vxyPlanForward.end(); itWaypoint++, waypointNumber++)
            {
                double latitude_deg(0.0);
                double longitude_deg(0.0);
                unitConversions.ConvertNorthEast_mToLatLong_deg(itWaypoint->x, itWaypoint->y, latitude_deg, longitude_deg);

                auto waypoint = new afrl::cmasi::Waypoint();
                waypoint->setNumber(waypointNumber);
                waypoint->setLatitude(latitude_deg);
                waypoint->setLongitude(longitude_deg);
                waypoint->setAltitude(itWaypoint->z);
                routePlan->getWaypoints().push_back(waypoint);
                waypoint = nullptr; // gave up ownership

                if (itWaypoint != vxyPlanForward.begin())
                {
                    // add to the length of the path
                    distance_m += itWaypoint->dist(*itWaypointlast);

                    if (itWaypointlast == vxyPlanForward.begin())
                    {
                        startHeading_deg = itWaypointlast->heading2d(*itWaypoint);
                        startHeading_deg = startHeading_deg * n_Const::c_Convert::dRadiansToDegrees();
                    }
                    else if ((itWaypoint + 1) == vxyPlanForward.end())
                    {
                        endHeading_deg = (itWaypointlast->heading2d(*itWaypoint) + n_Const::c_Convert::dPi()) * n_Const::c_Convert::dRadiansToDegrees();
                    }
                }
                itWaypointlast = itWaypoint;
            }

            m_optionIdVsDpss.insert(std::make_pair(pTaskOptionClass->m_taskOption->getOptionID(), dpss));

            int64_t routeId = TaskOptionClass::m_firstImplementationRouteId;
            routePlan->setRouteID(routeId);

            double cost_ms = static_cast<int64_t> (((pTaskOptionClass->m_speed_mps > 0.0) ? (distance_m / pTaskOptionClass->m_speed_mps) : (0.0))*1000.0);
            routePlan->setRouteCost(cost_ms);

            pTaskOptionClass->m_orderedRouteIdVsPlan[routePlan->getRouteID()] = routePlan;

            pTaskOptionClass->m_taskOption->setStartLocation(new afrl::cmasi::Location3D(*(routePlan->getWaypoints().front())));
            pTaskOptionClass->m_taskOption->setStartHeading(startHeading_deg);
            pTaskOptionClass->m_taskOption->setEndLocation(new afrl::cmasi::Location3D(*(routePlan->getWaypoints().back())));
            pTaskOptionClass->m_taskOption->setEndHeading(endHeading_deg);

            pTaskOptionClass->m_taskOption->setCost(cost_ms);

            m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());
        } //if((vxyPlanForward.size() > 1) && (vxyPlanReverse.size() > 1))
    }
    else //if(m_isUseDpss)
    {
        auto routePlan = std::make_shared<uxas::messages::route::RoutePlan>();
        int64_t waypointNumber = 1;
        double distance_m = 0.0;
        double northLast_m = 0.0;
        double eastLast_m = 0.0;
        double startHeading_deg = 0;
        double endHeading_deg = 0;

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
        double theta_rad = 0.0; //could be used to set a different starting heading
        double radius_m = 0.0;
        bool firstPass = true;
        while (radius_m <= m_patternSearchTask->getExtent())
        {
            radius_m = 0.5 * pTaskOptionClass->m_laneSpacing_m * (1.0 + theta_rad / n_Const::c_Convert::dPi());
            double north_m = (radius_m * sin(theta_rad - startHeading_deg)) + northStart_m;
            double east_m = (radius_m * cos(theta_rad - startHeading_deg)) + eastStart_m;
            double latitude_deg(0.0);
            double longitude_deg(0.0);
            if (firstPass)
            {
                // add a starting point that puts the leading edge of the sensor on the start of the spiral
                northLast_m = north_m - sensorFootprint->getHorizontalToLeadingEdge() * cos(startHeading_deg);
                eastLast_m = east_m - sensorFootprint->getHorizontalToLeadingEdge() * sin(startHeading_deg);
                unitConversions.ConvertNorthEast_mToLatLong_deg(northLast_m, eastLast_m,
                                                                latitude_deg, longitude_deg);
                auto waypoint = new afrl::cmasi::Waypoint();
                waypoint->setNumber(waypointNumber);
                waypoint->setLatitude(latitude_deg);
                waypoint->setLongitude(longitude_deg);
                waypoint->setAltitude(pTaskOptionClass->m_altitude_m);
                waypoint->setSpeed(pTaskOptionClass->m_speed_mps);
                routePlan->getWaypoints().push_back(waypoint);

                pTaskOptionClass->m_taskOption->setStartLocation(new afrl::cmasi::Location3D(*(waypoint)));
                pTaskOptionClass->m_taskOption->setStartHeading(startHeading_deg);

                waypoint = nullptr; // gave up ownership
                waypointNumber++; // next waypoint
            }
            unitConversions.ConvertNorthEast_mToLatLong_deg(north_m, east_m,
                                                            latitude_deg, longitude_deg);
            auto waypoint = new afrl::cmasi::Waypoint();
            waypoint->setNumber(waypointNumber);
            waypoint->setLatitude(latitude_deg);
            waypoint->setLongitude(longitude_deg);
            waypoint->setAltitude(pTaskOptionClass->m_altitude_m);
            waypoint->setSpeed(pTaskOptionClass->m_speed_mps);
            routePlan->getWaypoints().push_back(waypoint);
            waypoint = nullptr; // gave up ownership
            waypointNumber++; // next waypoint
            double deltaNorth_m = north_m - northLast_m;
            double deltaEast_m = east_m - eastLast_m;
            distance_m += pow((pow(deltaNorth_m, 2.0) + pow(deltaEast_m, 2.0)), 0.5);

            if (radius_m > 0.0) // divide by zero check
            {
                assert(m_waypointSpacing_m > 0.0);
                theta_rad += m_waypointSpacing_m / radius_m; // set the next theta based on the desired waypoint separation
            }
            if (radius_m > m_patternSearchTask->getExtent())
            {
                endHeading_deg = atan2(deltaEast_m, deltaNorth_m) * n_Const::c_Convert::dRadiansToDegrees();
            }
            northLast_m = north_m;
            eastLast_m = east_m;
            firstPass = false;
        }

        pTaskOptionClass->m_taskOption->setEndLocation(new afrl::cmasi::Location3D(*(routePlan->getWaypoints().back())));
        pTaskOptionClass->m_taskOption->setEndHeading(endHeading_deg);

        int64_t routeId = TaskOptionClass::m_firstImplementationRouteId;
        routePlan->setRouteID(routeId);

        double cost_ms = static_cast<int64_t> (((pTaskOptionClass->m_speed_mps > 0.0) ? (distance_m / pTaskOptionClass->m_speed_mps) : (0.0))*1000.0);
        routePlan->setRouteCost(cost_ms);

        pTaskOptionClass->m_orderedRouteIdVsPlan[routePlan->getRouteID()] = routePlan;

        pTaskOptionClass->m_taskOption->setStartLocation(new afrl::cmasi::Location3D(*(routePlan->getWaypoints().front())));
        pTaskOptionClass->m_taskOption->setStartHeading(startHeading_deg);
        pTaskOptionClass->m_taskOption->setEndLocation(new afrl::cmasi::Location3D(*(routePlan->getWaypoints().back())));
        pTaskOptionClass->m_taskOption->setEndHeading(endHeading_deg);

        pTaskOptionClass->m_taskOption->setCost(cost_ms);

        m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());
    } //if(m_isUseDpss)            

    return (isSuccess);
}

bool PatternSearchTaskService::isCalculatePatternScanRoute_Sector(std::shared_ptr<TaskOptionClass>& pTaskOptionClass,
                                                                  const std::unique_ptr<uxas::messages::task::SensorFootprint>& sensorFootprint,
                                                                  std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest)
{
    bool isSuccess(true);

    uxas::common::utilities::CUnitConversions unitConversions;
    double northStart_m = 0.0;
    double eastStart_m = 0.0;
    unitConversions.ConvertLatLong_degToNorthEast_m(m_patternSearchTask->getSearchLocation()->getLatitude(),
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
        unitConversions.ConvertNorthEast_mToLatLong_deg(searchSegment->m_startPosition.m_north_m,
                                                        searchSegment->m_startPosition.m_east_m, startLatitude_deg, startLongitude_deg);
        startLocation->setLatitude(startLatitude_deg);
        startLocation->setLongitude(startLongitude_deg);
        startLocation->setAltitude(pTaskOptionClass->m_altitude_m);

        auto endLocation = new afrl::cmasi::Location3D();
        double endLatitude_deg(0.0);
        double endLongitude_deg(0.0);
        unitConversions.ConvertNorthEast_mToLatLong_deg(searchSegment->m_endPosition.m_north_m,
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

    uxas::common::utilities::CUnitConversions unitConversions;
    double northStart_m = 0.0;
    double eastStart_m = 0.0;
    unitConversions.ConvertLatLong_degToNorthEast_m(m_patternSearchTask->getSearchLocation()->getLatitude(),
                                                    m_patternSearchTask->getSearchLocation()->getLongitude(), northStart_m, eastStart_m);

    return (isSuccess);
}

void PatternSearchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    uxas::common::utilities::CUnitConversions unitConversions;
    if (m_isUseDpss)
    {
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
            pGimbalStareAction->getAssociatedTaskList().push_back(m_patternSearchTask->getTaskID());
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
        else //if (m_isUseDpss && m_activeDpss)
        {
            //ERROR:: no DPSS
        } //if (m_isUseDpss && m_activeDpss)
    } //if(m_isUseDpss)
}
}; //namespace task
}; //namespace service
}; //namespace uxas

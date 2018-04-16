// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_CmasiLineSearch.cpp
 * Author: steve
 * 
 * Created on October 13, 2015, 6:17 PM
 */


#include "CmasiLineSearchTaskService.h"

#include "Position.h"
#include "UnitConversions.h"
#include "FileSystemUtilities.h"

#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RouteConstraints.h"
#include "uxas/messages/uxnative/VideoRecord.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <iomanip>  //setfill

#define STRING_XML_LINE_SEARCH_ONE_DIRECTION "LineSearchOneDirection"

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "CMLS-CMLS-CMLS-CMLS:: CmasiLineSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "CMLS-CMLS-CMLS-CMLS:: CmasiLineSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
CmasiLineSearchTaskService::ServiceBase::CreationRegistrar<CmasiLineSearchTaskService>
CmasiLineSearchTaskService::s_registrar(CmasiLineSearchTaskService::s_registryServiceTypeNames());

CmasiLineSearchTaskService::CmasiLineSearchTaskService()
: TaskServiceBase(CmasiLineSearchTaskService::s_typeName(), CmasiLineSearchTaskService::s_directoryName())
{
};

CmasiLineSearchTaskService::~CmasiLineSearchTaskService()
{
};

bool
CmasiLineSearchTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::cmasi::isLineSearchTask(m_task.get()))
        {
            m_lineSearchTask = std::static_pointer_cast<afrl::cmasi::LineSearchTask>(m_task);
            if (!m_lineSearchTask)
            {
                sstrErrors << "ERROR:: **CmasiLineSearchTaskService::bConfigure failed to cast a LineSearchTask from the task pointer." << std::endl;
                CERR_FILE_LINE_MSG(sstrErrors.str())
                isSuccessful = false;
            }
            else
            {
                //////////////////////////////////////////////
                //////////// PROCESS OPTIONS /////////////////
                pugi::xml_node ndTaskOptions = ndComponent.child(m_taskOptions_XmlTag.c_str());
                if (ndTaskOptions)
                {
                    for (pugi::xml_node ndTaskOption = ndTaskOptions.first_child(); ndTaskOption; ndTaskOption = ndTaskOption.next_sibling())
                    {
                        if (std::string(STRING_XML_LINE_SEARCH_ONE_DIRECTION) == ndTaskOption.name())
                        {
                            m_isPlanBothDirections = false;
                        }
                    }
                }
            }
        }
        else
        {
            sstrErrors << "ERROR:: **CmasiLineSearchTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a LineSearchTask." << std::endl;
            CERR_FILE_LINE_MSG(sstrErrors.str())
            isSuccessful = false;
        }
    } //isSuccessful
    return (isSuccessful);
}

void CmasiLineSearchTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

    double wedgeAzimuthIncrement(n_Const::c_Convert::dPiO8());
    double wedgeElevationIncrement(n_Const::c_Convert::dPiO8());

    int64_t optionId = TaskOptionClass::m_firstOptionId;
    int64_t taskId(m_lineSearchTask->getTaskID());

    double groundAltitude_m{0.0};
    double groundAltitudeTemp_m{100000.0}; //some big number
    for (auto& location : m_lineSearchTask->getPointList())
    {
        if (location->getAltitude() < groundAltitudeTemp_m)
        {
            groundAltitudeTemp_m = location->getAltitude();
        }
    }
    if (groundAltitudeTemp_m < 90000.0)
    {
        groundAltitude_m = groundAltitudeTemp_m;
    }
    std::string compositionString("+(");

    for (auto itEligibleEntities = m_speedAltitudeVsEligibleEntityIdsRequested.begin(); itEligibleEntities != m_speedAltitudeVsEligibleEntityIdsRequested.end(); itEligibleEntities++)
    {
        //ViewAngleList
        if (!m_lineSearchTask->getViewAngleList().empty())
        {
            // Elevation is measured from the horizon, positive up
            // TODO use min/max values in AirVehicleConfiguration
            auto elevationMin_rad = -90.0 * n_Const::c_Convert::dDegreesToRadians();
            auto elevationMax_rad = 10.0 * n_Const::c_Convert::dDegreesToRadians();
                

            for (auto itWedge = m_lineSearchTask->getViewAngleList().begin();
                    itWedge != m_lineSearchTask->getViewAngleList().end();
                    itWedge++)
            {

                double elevationLookAngleCenterline_rad = (*itWedge)->getVerticalCenterline() * n_Const::c_Convert::dDegreesToRadians();
                elevationLookAngleCenterline_rad = (elevationLookAngleCenterline_rad < elevationMin_rad) ? (elevationMin_rad) : (elevationLookAngleCenterline_rad);
                elevationLookAngleCenterline_rad = (elevationLookAngleCenterline_rad > elevationMax_rad) ? (elevationMax_rad) : (elevationLookAngleCenterline_rad);
                //vertical centerline angle is between elevationMin_rad and elevationMax_rad

                double elevationLookAngleStart_rad = elevationLookAngleCenterline_rad - (((*itWedge)->getVerticalExtent() / 2.0) * n_Const::c_Convert::dDegreesToRadians());
                elevationLookAngleStart_rad = (elevationLookAngleStart_rad < elevationMin_rad) ? (elevationMin_rad) : (elevationLookAngleStart_rad);

                double elevationLookAngleEnd_rad = elevationLookAngleCenterline_rad + (((*itWedge)->getVerticalExtent() / 2.0) * n_Const::c_Convert::dDegreesToRadians());
                elevationLookAngleEnd_rad = (elevationLookAngleEnd_rad > elevationMax_rad) ? (elevationMax_rad) : (elevationLookAngleEnd_rad);

                double elevationLookAngleCurrent_rad(elevationLookAngleStart_rad);
                while (n_Const::c_Convert::bCompareDouble(elevationLookAngleEnd_rad, elevationLookAngleCurrent_rad, n_Const::c_Convert::enGreaterEqual))
                {
                    double dHeadingCenterline_rad = n_Const::c_Convert::dNormalizeAngleRad(((*itWedge)->getAzimuthCenterline() * n_Const::c_Convert::dDegreesToRadians()), 0.0);
                    //centerline angle is between 0 and 2PI
                    double dHeadingStart_rad = dHeadingCenterline_rad - ((*itWedge)->getAzimuthExtent() / 2.0) * n_Const::c_Convert::dDegreesToRadians();
                    double dHeadingEnd_rad = dHeadingCenterline_rad + ((*itWedge)->getAzimuthExtent() / 2.0) * n_Const::c_Convert::dDegreesToRadians();
                    double dHeadingCurrent_rad(dHeadingStart_rad);
                    double dHeadingTarget_rad = (n_Const::c_Convert::bCompareDouble(dHeadingEnd_rad, dHeadingStart_rad, n_Const::c_Convert::enGreaterEqual, 1.0e-5)) ? (dHeadingEnd_rad) : (n_Const::c_Convert::dTwoPi());
                    while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
                    {
                        double nominalAltitude_m = itEligibleEntities->first.second - groundAltitude_m;
                        std::string algebraString;
                        if (isCalculateOption(taskId, itEligibleEntities->second,
                                nominalAltitude_m, itEligibleEntities->first.first,
                                dHeadingCurrent_rad, elevationLookAngleCurrent_rad,
                                optionId, algebraString))
                        {
                            compositionString += algebraString + " ";
                            optionId++;
                        }
                        dHeadingCurrent_rad += wedgeAzimuthIncrement;
                    }
                    //need to see if wedge straddles the 0/2PI direction
                    if ((!n_Const::c_Convert::bCompareDouble(dHeadingEnd_rad, dHeadingTarget_rad, n_Const::c_Convert::enEqual)) &&
                            (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, n_Const::c_Convert::dTwoPi(), n_Const::c_Convert::enEqual)))
                    {
                        dHeadingCurrent_rad = 0.0;
                        dHeadingTarget_rad = dHeadingEnd_rad;
                        while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
                        {
                            double nominalAltitude_m = itEligibleEntities->first.second - groundAltitude_m;
                            std::string algebraString;
                            if (isCalculateOption(taskId, itEligibleEntities->second,
                                    nominalAltitude_m, itEligibleEntities->first.first,
                                    dHeadingCurrent_rad, elevationLookAngleCurrent_rad,
                                    optionId, algebraString))
                            {
                                compositionString += algebraString + " ";
                                optionId++;
                            }
                            dHeadingCurrent_rad += wedgeAzimuthIncrement;
                        }
                    }
                    elevationLookAngleCurrent_rad += wedgeElevationIncrement;
                } //while (n_Const::c_Convert::bCompareDouble(dVerticalTarget_rad, dVerticalCu
            } //for (auto itWedge = m_lineSearchTask->getViewA ... 
        }
        else
        {
            // no set wedge, so use default angles
            double nominalAltitude_m = itEligibleEntities->first.second - groundAltitude_m;
            std::string algebraString;
            if (isCalculateOption(taskId, itEligibleEntities->second,
                    nominalAltitude_m, itEligibleEntities->first.first,
                    m_defaultAzimuthLookAngle_rad, m_defaultElevationLookAngle_rad,
                    optionId, algebraString))
            {
                compositionString += algebraString + " ";
                optionId++;
            }
        }
    } //for(auto itEligibleEntities=m_speedAltitudeVsEligibleEntitesRequested.begin();itEl ... 

    compositionString += ")";

    m_taskPlanOptions->setComposition(compositionString);

    // send out the options
    if (isSuccessful)
    {
        auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
        sendSharedLmcpObjectBroadcastMessage(newResponse);
    }
};


#ifdef STEVETEST
//GSD
rObjParameters_PatrolSegment_DPSS.dGetGroundSampleDistance_m() = dGetGroundSampleDistance_m();
if (dGetGroundSampleDistance_m() > 0.0)
{
    rObjParameters_PatrolSegment_DPSS.bGetUseGroundSampleDistance() = true;
}
else
{
    rObjParameters_PatrolSegment_DPSS.bGetUseGroundSampleDistance() = false;
}
#endif  //STEVETEST

bool CmasiLineSearchTaskService::isCalculateOption(const int64_t& taskId, const std::vector<int64_t>& eligibleEntities,
        const double& nominalAltitude_m, const double& nominalSpeed_mps,
        const double& azimuthLookAngle_rad, const double& elevationLookAngle_rad,
        int64_t& optionId, std::string& algebraString)
{
    bool isSuccess(true);

    std::vector<Dpss_Data_n::xyPoint> vxyTrueRoad;
    int32_t maxNumberWaypointsPoints{0};
    uxas::common::utilities::CUnitConversions unitConversions;

    if (m_lineSearchTask->getPointList().size() > 1)
    {
        //0) Initialize DPSS
        //1) Get Waypoints from DPSS

        std::vector<Dpss_Data_n::xyPoint> vxyTrueWaypoints;
        ///////////////////////////////////////////////
        //0) Initialize DPSS
        uint32_t pointId(1); // road point Id's for DPSS
        for (auto itPoint = m_lineSearchTask->getPointList().begin();
                itPoint != m_lineSearchTask->getPointList().end();
                itPoint++)
        {
            double north_m(0.0);
            double east_m(0.0);
            unitConversions.ConvertLatLong_degToNorthEast_m((*itPoint)->getLatitude(), (*itPoint)->getLongitude(), north_m, east_m);

            Dpss_Data_n::xyPoint xyTemp(north_m, east_m, (*itPoint)->getAltitude());
            xyTemp.id = pointId;
            vxyTrueRoad.push_back(xyTemp);
            pointId++;
        }
        vxyTrueWaypoints = vxyTrueRoad;

        // calculate length of road
        double dLengthRoad(0.0);
        auto itPointFirst = vxyTrueRoad.begin();
        auto itPointSecond = vxyTrueRoad.begin() + 1;
        for (; (itPointFirst != vxyTrueRoad.end() && itPointSecond != vxyTrueRoad.end()); itPointFirst++, itPointSecond++)
        {
            dLengthRoad += itPointSecond->dist(*itPointFirst);
        }

        maxNumberWaypointsPoints = static_cast<int32_t> (dLengthRoad / 200.0); // 200 meter segments
        maxNumberWaypointsPoints = (maxNumberWaypointsPoints < 2) ? (2) : (maxNumberWaypointsPoints); // need at least two points

        // first reset the Dpss
        auto dpss = std::make_shared<Dpss>();
        std::string dpssPath = m_strSavePath + "DPSS_Output/OptionId_" + std::to_string(optionId) + "/";
        dpss->SetOutputPath(dpssPath.c_str());
        dpss->SetSingleDirectionPlanning(true);

        //1.1) Call DPSS Plan the path (quickly)
        dpss->PreProcessPath(vxyTrueWaypoints);

        // need non-const versions of these 
        auto localAzimuthLookAngle_rad = azimuthLookAngle_rad;
        auto localElevationLookAngle_rad = elevationLookAngle_rad;
        auto localNominalAltitude_m = nominalAltitude_m;

        dpss->SetNominalAzimuth_rad(localAzimuthLookAngle_rad);
        dpss->SetNominalElevation_rad(localElevationLookAngle_rad);
        dpss->SetNominalAltitude_m(localNominalAltitude_m);

        dpss->PlanQuickly(vxyTrueWaypoints, maxNumberWaypointsPoints);

        //1.2) Offset the Path in Forward and reverse directions

        //1.2.1) Call DPSS Offset Path Forward
        std::vector<Dpss_Data_n::xyPoint> vxyPlanForward;
        dpss->OffsetPlanForward(vxyTrueWaypoints, vxyPlanForward);

        if (vxyPlanForward.size() > 1)
        {
            std::vector<Dpss_Data_n::xyPoint> vxyPlanComplete;
            vxyPlanComplete = vxyPlanForward;


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


            //build the options
            algebraString += "+(";
            algebraString += "p" + std::to_string(optionId) + " ";

            // build the forward waypoints && calculate cost
            auto routePlanForward = std::make_shared<uxas::messages::route::RoutePlan>();
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
                routePlanForward->getWaypoints().push_back(waypoint);
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
                    if ((itWaypoint + 1) == vxyPlanForward.end())
                    {
                        endHeading_deg = itWaypointlast->heading2d(*itWaypoint) * n_Const::c_Convert::dRadiansToDegrees();
                    }
                }
                itWaypointlast = itWaypoint;
            }

            int64_t routeId = TaskOptionClass::m_firstImplementationRouteId;

            routePlanForward->setRouteID(routeId);

            double costForward_ms = static_cast<int64_t> (((nominalSpeed_mps > 0.0) ? (distance_m / nominalSpeed_mps) : (0.0))*1000.0);
            routePlanForward->setRouteCost(costForward_ms);

            m_optionIdVsDpss.insert(std::make_pair(optionId, dpss));

            auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
            auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
            pTaskOptionClass->m_taskOption->setTaskID(taskId);
            pTaskOptionClass->m_taskOption->setOptionID(optionId);
            pTaskOptionClass->m_taskOption->setCost(costForward_ms);
            pTaskOptionClass->m_taskOption->setStartLocation(routePlanForward->getWaypoints().front()->clone());
            pTaskOptionClass->m_taskOption->setStartHeading(startHeading_deg);
            pTaskOptionClass->m_taskOption->setEndLocation(routePlanForward->getWaypoints().back()->clone());
            pTaskOptionClass->m_taskOption->setEndHeading(endHeading_deg);
            pTaskOptionClass->m_taskOption->getEligibleEntities() = eligibleEntities; // defaults to all entities eligible
            pTaskOptionClass->m_orderedRouteIdVsPlan[routePlanForward->getRouteID()] = routePlanForward;
            m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
            m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());
            routeId++;
            optionId++;
        }
        else //if((vxyPlanForward.size() > 1) && (vxyPlanReverse.size() > 1))
        {
            isSuccess = false;
            CERR_FILE_LINE_MSG("ERROR::initializeDpss:: less than two waypoints points generated for forward and/or reverse plan(s)!")
        }
    }
    else //if(!rObjParameters_PatrolSegment_DPSS.vwayGetPathPoints().empty())
    {
        isSuccess = false;
        CERR_FILE_LINE_MSG("ERROR::initializeDpss:: less than two road points passed in!")
    } //if(!rObjParameters_PatrolSegment_DPSS.vwayGetPathPoints().empty())
    
    if (isSuccess && m_isPlanBothDirections)
    {
        //0) Initialize DPSS
        //1) Get Waypoints from DPSS
        std::vector<Dpss_Data_n::xyPoint> vxyTrueRoad2;
        std::vector<Dpss_Data_n::xyPoint> vxyTrueWaypoints;

        for (auto itPoint = vxyTrueRoad.rbegin();
                itPoint != vxyTrueRoad.rend();
                itPoint++)
        {
            Dpss_Data_n::xyPoint xyTemp(itPoint->x,itPoint->y, itPoint->z);
            xyTemp.id = itPoint->id;
            vxyTrueRoad2.push_back(xyTemp);
        }
        vxyTrueWaypoints = vxyTrueRoad2;

        // calculate length of road
        double dLengthRoad(0.0);
        auto itPointFirst = vxyTrueRoad2.begin();
        auto itPointSecond = vxyTrueRoad2.begin() + 1;
        for (; (itPointFirst != vxyTrueRoad2.end() && itPointSecond != vxyTrueRoad2.end()); itPointFirst++, itPointSecond++)
        {
            dLengthRoad += itPointSecond->dist(*itPointFirst);
        }

        int32_t maxNumberWaypointsPoints = static_cast<int32_t> (dLengthRoad / 200.0); // 200 meter segments
        maxNumberWaypointsPoints = (maxNumberWaypointsPoints < 2) ? (2) : (maxNumberWaypointsPoints); // need at least two points

        // first reset the Dpss
        auto dpss = std::make_shared<Dpss>();
        std::string dpssPath = m_strSavePath + "DPSS_Output/OptionId_" + std::to_string(optionId) + "/";
        dpss->SetOutputPath(dpssPath.c_str());
        dpss->SetSingleDirectionPlanning(true);

        //1.1) Call DPSS Plan the path (quickly)
        dpss->PreProcessPath(vxyTrueWaypoints);

        // need non-const versions of these 
        auto localAzimuthLookAngle_rad = azimuthLookAngle_rad;
        auto localElevationLookAngle_rad = elevationLookAngle_rad;
        auto localNominalAltitude_m = nominalAltitude_m;

        dpss->SetNominalAzimuth_rad(localAzimuthLookAngle_rad);
        dpss->SetNominalElevation_rad(localElevationLookAngle_rad);
        dpss->SetNominalAltitude_m(localNominalAltitude_m);

        dpss->PlanQuickly(vxyTrueWaypoints, maxNumberWaypointsPoints);

        //1.2) Offset the Path in Forward and reverse directions

        //1.2.1) Call DPSS Offset Path Forward
        std::vector<Dpss_Data_n::xyPoint> vxyPlanForward;
        dpss->OffsetPlanForward(vxyTrueWaypoints, vxyPlanForward);

        if (vxyPlanForward.size() > 1)
        {
            std::vector<Dpss_Data_n::xyPoint> vxyPlanComplete;
            vxyPlanComplete = vxyPlanForward;


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
            dpss->SetObjective(vxyTrueRoad2, vxyPlanComplete, &op);


            //build the options
            algebraString += "p" + std::to_string(optionId) + " ";

            // build the forward waypoints && calculate cost
            auto routePlanForward = std::make_shared<uxas::messages::route::RoutePlan>();
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
                routePlanForward->getWaypoints().push_back(waypoint);
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
                    if ((itWaypoint + 1) == vxyPlanForward.end())
                    {
                        endHeading_deg = itWaypointlast->heading2d(*itWaypoint) * n_Const::c_Convert::dRadiansToDegrees();
                    }
                }
                itWaypointlast = itWaypoint;
            }

            int64_t routeId = TaskOptionClass::m_firstImplementationRouteId;

            routePlanForward->setRouteID(routeId);

            double costForward_ms = static_cast<int64_t> (((nominalSpeed_mps > 0.0) ? (distance_m / nominalSpeed_mps) : (0.0))*1000.0);
            routePlanForward->setRouteCost(costForward_ms);

            m_optionIdVsDpss.insert(std::make_pair(optionId, dpss));

            auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
            auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
            pTaskOptionClass->m_taskOption->setTaskID(taskId);
            pTaskOptionClass->m_taskOption->setOptionID(optionId);
            pTaskOptionClass->m_taskOption->setCost(costForward_ms);
            pTaskOptionClass->m_taskOption->setStartLocation(routePlanForward->getWaypoints().front()->clone());
            pTaskOptionClass->m_taskOption->setStartHeading(startHeading_deg);
            pTaskOptionClass->m_taskOption->setEndLocation(routePlanForward->getWaypoints().back()->clone());
            pTaskOptionClass->m_taskOption->setEndHeading(endHeading_deg);
            pTaskOptionClass->m_taskOption->getEligibleEntities() = eligibleEntities; // defaults to all entities eligible
            pTaskOptionClass->m_orderedRouteIdVsPlan[routePlanForward->getRouteID()] = routePlanForward;
            m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
            m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());
            routeId++;
            optionId++;
        }
        else //if((vxyPlanForward.size() > 1) && (vxyPlanReverse.size() > 1))
        {
            isSuccess = false;
            CERR_FILE_LINE_MSG("ERROR::initializeDpss:: less than two waypoints points generated for forward and/or reverse plan(s)!")
        }
    } // if(isSuccess)
    if (isSuccess)
    {
        algebraString += ")";
    }
    return (isSuccess);
};

bool CmasiLineSearchTaskService::isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse, std::shared_ptr<TaskOptionClass>& taskOptionClass,
        int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route)
{
    auto itDpss = m_optionIdVsDpss.find(taskOptionClass->m_taskOption->getOptionID());
    if (itDpss != m_optionIdVsDpss.end())
    {
        m_activeDpss = itDpss->second;
    }
    else //if(itDpss != m_optionIdVsDpss.end())
    {
        CERR_FILE_LINE_MSG("ERROR::CmasiLineSearchTaskService::processRouteResponse: for TaskId[" << m_lineSearchTask->getTaskID()
                << "] could not find a DPSS for OptionId[" << taskOptionClass->m_taskOption->getOptionID() << "].")
    } //if(itDpss != m_optionIdVsDpss.end())
    return (false); // want the base class to build the response
}

void CmasiLineSearchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    if (m_activeDpss)
    {
        uxas::common::utilities::CUnitConversions unitConversions;
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

        double dLatitude_deg(0.0);
        double dLongitude_deg(0.0);
        unitConversions.ConvertNorthEast_mToLatLong_deg(xyStarePoint.x, xyStarePoint.y, dLatitude_deg, dLongitude_deg);

        //point the gimbal
        auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
        vehicleActionCommand->setVehicleID(entityState->getID());

        afrl::cmasi::GimbalStareAction* pGimbalStareAction = new afrl::cmasi::GimbalStareAction();
        pGimbalStareAction->setPayloadID(gimbalPayloadId);
        pGimbalStareAction->getAssociatedTaskList().push_back(m_lineSearchTask->getTaskID());
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
}


}; //namespace task
}; //namespace service
}; //namespace uxas

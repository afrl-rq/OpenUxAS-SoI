// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_ImpactPointSearch.cpp
 * Author: steve
 * 
 * Created on February 12, 2015, 6:17 PM
 */


#include "ImpactPointSearchTaskService.h"

#include "Position.h"
#include "UnitConversions.h"

#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RouteResponse.h"
#include "uxas/messages/route/RouteConstraints.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <afrl/cmasi/GimbalConfiguration.h>


#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "IMPCT_PS-IMPCT_PS-IMPCT_PS-IMPCT_PS:: ImpactPointSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "IMPCT_PS-IMPCT_PS-IMPCT_PS-IMPCT_PS:: ImpactPointSearch:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
ImpactPointSearchTaskService::ServiceBase::CreationRegistrar<ImpactPointSearchTaskService>
ImpactPointSearchTaskService::s_registrar(ImpactPointSearchTaskService::s_registryServiceTypeNames());

ImpactPointSearchTaskService::ImpactPointSearchTaskService()
: TaskServiceBase(ImpactPointSearchTaskService::s_typeName(), ImpactPointSearchTaskService::s_directoryName()) { };

ImpactPointSearchTaskService::~ImpactPointSearchTaskService() { };

bool
ImpactPointSearchTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isImpactPointSearchTask(m_task.get()))
        {
            m_pointSearchTask = std::static_pointer_cast<afrl::impact::ImpactPointSearchTask>(m_task);
            if (!m_pointSearchTask)
            {
                sstrErrors << "ERROR:: **ImpactPointSearchTaskService::bConfigure failed to cast a ImpactPointSearchTask from the task pointer." << std::endl;
                CERR_FILE_LINE_MSG(sstrErrors.str())
                isSuccessful = false;
            }
            if (m_pointSearchTask->getSearchLocationID() > 0)
            {
                auto foundPoint = m_pointsOfInterest.find(m_pointSearchTask->getSearchLocationID());
                if (foundPoint != m_pointsOfInterest.end())
                {
                    m_pointOfInterest = foundPoint->second;
                    m_pointSearchTask->setSearchLocation(m_pointOfInterest->getLocation()->clone());
                }
                else
                {
                    sstrErrors << "ERROR:: **ImpactPointSearchTaskService::bConfigure PointOfInterest [" << m_pointSearchTask->getSearchLocationID() << "] was not found." << std::endl;
                    CERR_FILE_LINE_MSG(sstrErrors.str())
                    isSuccessful = false;
                }
            }
        }
        else
        {
            sstrErrors << "ERROR:: **ImpactPointSearchTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a ImpactPointSearchTask." << std::endl;
            CERR_FILE_LINE_MSG(sstrErrors.str())
            isSuccessful = false;
        }
    } //isSuccessful
    return (isSuccessful);
}

void ImpactPointSearchTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

    int64_t optionId(1);
    int64_t taskId(m_pointSearchTask->getTaskID());

    auto standoffDistance = m_pointSearchTask->getStandoffDistance();
    if (n_Const::c_Convert::bCompareDouble(standoffDistance, 0.0, n_Const::c_Convert::enLess))
    {
        if (isCalculateOption(taskId, optionId, 0.0))
        {
            optionId++;
        }
    }
    else
    {
        double wedgeDirectionIncrement(n_Const::c_Convert::dPiO8());

        //ViewAngleList
        if (!m_pointSearchTask->getViewAngleList().empty())
        {
            for (auto itWedge = m_pointSearchTask->getViewAngleList().begin();
                    itWedge != m_pointSearchTask->getViewAngleList().end();
                    itWedge++)
            {
                double dHeadingCenterline_rad = n_Const::c_Convert::dNormalizeAngleRad(((*itWedge)->getAzimuthCenterline() * n_Const::c_Convert::dDegreesToRadians()), 0.0);
                //centerline angle is between 0 and 2PI
                double dHeadingStart_rad = dHeadingCenterline_rad - ((*itWedge)->getAzimuthExtent() / 2.0) * n_Const::c_Convert::dDegreesToRadians();
                double dHeadingEnd_rad = dHeadingCenterline_rad + ((*itWedge)->getAzimuthExtent() / 2.0) * n_Const::c_Convert::dDegreesToRadians();
                double dHeadingCurrent_rad(dHeadingStart_rad);
                double dHeadingTarget_rad = (n_Const::c_Convert::bCompareDouble(dHeadingEnd_rad, dHeadingStart_rad, n_Const::c_Convert::enGreaterEqual, 1.0e-5)) ? (dHeadingEnd_rad) : (n_Const::c_Convert::dTwoPi());
                while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
                {
                    if (isCalculateOption(taskId, optionId, dHeadingCurrent_rad))
                    {
                        optionId++;
                    }
                    dHeadingCurrent_rad += wedgeDirectionIncrement;
                }
                //need to see if wedge straddles the 0/2PI direction
                if ((!n_Const::c_Convert::bCompareDouble(dHeadingEnd_rad, dHeadingTarget_rad, n_Const::c_Convert::enEqual)) &&
                        (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, n_Const::c_Convert::dTwoPi(), n_Const::c_Convert::enEqual)))
                {
                    dHeadingCurrent_rad = 0.0;
                    dHeadingTarget_rad = dHeadingEnd_rad;
                    while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
                    {
                        if (isCalculateOption(taskId, optionId, dHeadingCurrent_rad))
                        {
                            optionId++;
                        }
                        dHeadingCurrent_rad += wedgeDirectionIncrement;
                    }
                }
            }
        }
        else
        {
            // no set wedge, so standoff from any angle
            double dHeadingCurrent_rad = 0.0;
            double dHeadingTarget_rad = n_Const::c_Convert::dTwoPi() - wedgeDirectionIncrement;
            while (n_Const::c_Convert::bCompareDouble(dHeadingTarget_rad, dHeadingCurrent_rad, n_Const::c_Convert::enGreaterEqual))
            {
                if (isCalculateOption(taskId, optionId, dHeadingCurrent_rad))
                {
                    optionId++;
                }
                dHeadingCurrent_rad += wedgeDirectionIncrement;
            }
        }
    }

    std::string compositionString("+(");
    for (auto itOption = m_taskPlanOptions->getOptions().begin(); itOption != m_taskPlanOptions->getOptions().end(); itOption++)
    {
        compositionString += "p";
        compositionString += std::to_string((*itOption)->getOptionID());
        compositionString += " ";
    }
    compositionString += ")";

    m_taskPlanOptions->setComposition(compositionString);

    // send out the options
    if (isSuccessful)
    {
        auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
        sendSharedLmcpObjectBroadcastMessage(newResponse);
    }
};

bool ImpactPointSearchTaskService::isCalculateOption(const int64_t& taskId, int64_t& optionId, const double& wedgeHeading_rad)
{
    bool isSuccessful{true};

    uxas::common::utilities::CUnitConversions unitConversions;
    auto standoffDistance = m_pointSearchTask->getStandoffDistance();

    auto taskOption = new uxas::messages::task::TaskOption;
    auto startEndHeading_deg = n_Const::c_Convert::dNormalizeAngleRad((wedgeHeading_rad + n_Const::c_Convert::dPi()), 0.0) * n_Const::c_Convert::dRadiansToDegrees(); // [0,2PI) 
    taskOption->setStartHeading(startEndHeading_deg);
    taskOption->setEndHeading(startEndHeading_deg);

    if (n_Const::c_Convert::bCompareDouble(standoffDistance, 0.0, n_Const::c_Convert::enLessEqual))
    {
        taskOption->setTaskID(taskId);
        taskOption->setOptionID(optionId);
        //taskOption->setCost();    // defaults to 0.0
        taskOption->setStartLocation(m_pointSearchTask->getSearchLocation()->clone());
        taskOption->setEndLocation(m_pointSearchTask->getSearchLocation()->clone());
        //            for(auto itEligibleEntities=m_speedAltitudeVsEligibleEntitesRequested.begin();itEligibleEntities!=m_speedAltitudeVsEligibleEntitesRequested.end();itEligibleEntities++)
        //            {
        //                taskOption->getEligibleEntities().insert(taskOption->getEligibleEntities().end(),itEligibleEntities->second.begin(),itEligibleEntities->second.end());
        //            }
        //taskOption->getEligibleEntities();    // defaults to all entities eligible
        //taskOption->setCost(0);
        auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
        m_taskPlanOptions->getOptions().push_back(taskOption);
        taskOption = nullptr; //just gave up ownership
    }
    else
    {
        taskOption->setTaskID(taskId);
        taskOption->setOptionID(optionId);

        //find standoff (start) location/
        n_FrameworkLib::CPosition position(m_pointSearchTask->getSearchLocation()->getLatitude() * n_Const::c_Convert::dDegreesToRadians(),
                                           m_pointSearchTask->getSearchLocation()->getLongitude() * n_Const::c_Convert::dDegreesToRadians(),
                                           0.0, 0.0);
        double newNorth_m = standoffDistance * cos(wedgeHeading_rad) + position.m_north_m;
        double newEast_m = standoffDistance * sin(wedgeHeading_rad) + position.m_east_m;
        double latitude_rad(0.0);
        double longitude_rad(0.0);

        unitConversions.ConvertNorthEast_mToLatLong_rad(newNorth_m, newEast_m, latitude_rad, longitude_rad);
        auto startLocation = new afrl::cmasi::Location3D();
        startLocation->setLatitude(latitude_rad * n_Const::c_Convert::dRadiansToDegrees());
        startLocation->setLongitude(longitude_rad * n_Const::c_Convert::dRadiansToDegrees());
        taskOption->setStartLocation(startLocation);
        startLocation = nullptr; // just gave up ownership
        taskOption->setEndLocation(m_pointSearchTask->getSearchLocation()->clone());

        auto routePlan = std::make_shared<uxas::messages::route::RoutePlan>();

        int64_t waypointNumber = 1;
        auto waypoint = new afrl::cmasi::Waypoint();
        waypoint->setNumber(waypointNumber);
        waypoint->setLatitude(taskOption->getStartLocation()->getLatitude());
        waypoint->setLongitude(taskOption->getStartLocation()->getLongitude());
        waypoint->setAltitude(taskOption->getStartLocation()->getAltitude());
        routePlan->getWaypoints().push_back(waypoint);
        waypoint = nullptr; // gave up ownership
        
        waypointNumber++;
        waypoint = new afrl::cmasi::Waypoint();
        waypoint->setNumber(waypointNumber);
        waypoint->setLatitude(taskOption->getEndLocation()->getLatitude());
        waypoint->setLongitude(taskOption->getEndLocation()->getLongitude());
        waypoint->setAltitude(taskOption->getEndLocation()->getAltitude());
        routePlan->getWaypoints().push_back(waypoint);
        int64_t routeId = TaskOptionClass::m_firstImplementationRouteId;

        routePlan->setRouteID(routeId);
//        double costForward_ms = static_cast<int64_t> (((nominalSpeed_mps > 0.0) ? (standoffDistance / nominalSpeed_mps) : (0.0))*1000.0);
        int64_t costForward_ms = 0;
        routePlan->setRouteCost(costForward_ms);


        auto taskOptionLocal = taskOption->clone();
        taskOptionLocal->setOptionID(optionId);
        for (auto itEligibleEntites = m_speedAltitudeVsEligibleEntityIdsRequested.begin(); itEligibleEntites != m_speedAltitudeVsEligibleEntityIdsRequested.end(); itEligibleEntites++)
        {
            taskOptionLocal->getEligibleEntities() = itEligibleEntites->second;
            if (itEligibleEntites->first.first > 0)
            {
                taskOptionLocal->setCost(static_cast<int32_t> (standoffDistance) / itEligibleEntites->first.first);
            }
            auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOptionLocal->clone());
            auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
            pTaskOptionClass->m_orderedRouteIdVsPlan[routePlan->getRouteID()] = routePlan;
            m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
            m_taskPlanOptions->getOptions().push_back(taskOptionLocal);
            // start a new option
            optionId++;
            taskOptionLocal = taskOption->clone();
            taskOptionLocal->setOptionID(optionId);
        } //for(auto itSpeedId=m_speedVsVehicleId.begin();itSpeedId!=m_speedVsVehicleId.end();itSpeedId++)
        if (taskOptionLocal != nullptr)
        {
            delete taskOptionLocal;
            taskOptionLocal = nullptr;
        }
        if (taskOption != nullptr)
        {
            delete taskOption;
            taskOption = nullptr;
        }
    }

    return (isSuccessful);
}

bool ImpactPointSearchTaskService::isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse, std::shared_ptr<TaskOptionClass>& taskOptionClass,
                                                                            int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route)
{
	//add the desired action, if any
	if (!taskImplementationResponse->getTaskWaypoints().empty() && (m_pointSearchTask->getDesiredAction() != nullptr))
	{
		if (m_entityStates.find(taskImplementationResponse.get()->getVehicleID()) != m_entityStates.end())
		{
			auto lastWaypoint = taskImplementationResponse->getTaskWaypoints().back();
			m_pointSearchTask->getDesiredAction()->getLocation()->setAltitude(lastWaypoint->getAltitude());

			auto finalWaypoint = taskImplementationResponse->getTaskWaypoints().back();
			finalWaypoint->getVehicleActionList().push_back(m_pointSearchTask->getDesiredAction()->clone());

			//set up a gimbal stare action
			auto gimbalStareAction = std::make_shared<afrl::cmasi::GimbalStareAction>();
			gimbalStareAction->setStarepoint(m_pointSearchTask->getSearchLocation()->clone());
			if (m_entityConfigurations.find(taskImplementationResponse.get()->getVehicleID()) != m_entityConfigurations.end())
			{
				auto config = m_entityConfigurations[taskImplementationResponse.get()->getVehicleID()];
				for (auto payload : config->getPayloadConfigurationList())
				{
					if (afrl::cmasi::isGimbalConfiguration(payload))
					{
						gimbalStareAction->setPayloadID(payload->getPayloadID());
					}
				}
			}
			finalWaypoint->getVehicleActionList().push_back(gimbalStareAction->clone());
		}
	}
	return (false); // want the base class to build the response
}

void ImpactPointSearchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
}


}; //namespace task
}; //namespace service
}; //namespace uxas

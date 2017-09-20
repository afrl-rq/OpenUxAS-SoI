// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
* File:   LoiterTaskService.h
* Author: colin
*
* Created on May 4, 2017
*/

#ifndef UXAS_SERVICE_TASK_LOITER_TASK_SERVICE_H
#define UXAS_SERVICE_TASK_LOITER_TASK_SERVICE_H

#include "UnitConversions.h"

#include "afrl/cmasi/MustFlyTask.h"
#include "uxas/messages/route/RouteRequest.h"

#include <cstdint> // int64_t
#include <unordered_map>
#include "TaskServiceBase.h"
#include "afrl/cmasi/LoiterTask.h"

namespace uxas
{
namespace service
{
namespace task
{

/*! \class c_Task_LoiterTaskService
\brief A component that implements the CMASI LoiterTask
*/

class LoiterTaskService : public TaskServiceBase
{
public:

	static const std::string&
		s_typeName()
	{
		static std::string s_string("LoiterTaskService");
		return (s_string);
	};

	static const std::vector<std::string>
		s_registryServiceTypeNames()
	{
		std::vector<std::string> registryServiceTypeNames = { s_typeName(), "afrl.cmasi.LoiterTask" };
		return (registryServiceTypeNames);
	};

	static const std::string&
		s_directoryName()
	{
		static std::string s_string("");
		return (s_string);
	};

	static ServiceBase*
		create()
	{
		return new LoiterTaskService;
	};

	LoiterTaskService();

	virtual
		~LoiterTaskService();

private:

	static
		ServiceBase::CreationRegistrar<LoiterTaskService> s_registrar;

	/** brief Copy construction not permitted */
	LoiterTaskService(LoiterTaskService const&) = delete;

	/** brief Copy assignment operation not permitted */
	void operator=(LoiterTaskService const&) = delete;

private:

	bool configureTask(const pugi::xml_node& serviceXmlNode) override;

	bool processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;


public:
	const double m_defaultElevationLookAngle_rad = 60.0 * n_Const::c_Convert::dDegreesToRadians(); //60 deg down

public: //virtual

	virtual void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) override;
	virtual void buildTaskPlanOptions() override;
	virtual bool isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse, std::shared_ptr<TaskOptionClass>& taskOptionClass,
		int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route) override;

private:
	bool isCalculateOption(const std::vector<int64_t>& eligibleEntities,
		const double& nominalAltitude_m, const double& nominalSpeed_mps,
		const double& searchHeading_rad, const double& elevationLookAngle_rad,
		int64_t& optionId, std::string & algebraString); //NOTE:: optionId can be returned, changed, algebra string is returned
	bool isCalculateRasterScanRoute(std::shared_ptr<TaskOptionClass>& taskOptionClass, const double& laneSpacing_m,
		const double& sensorHorizontalToLeadingEdge_m, const double& sensorHorizontalToTrailingEdge_m,
		std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest);

private:
	std::shared_ptr<afrl::cmasi::LoiterTask> m_loiterTask;

};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_LOITER_TASK_SERVICE_H */


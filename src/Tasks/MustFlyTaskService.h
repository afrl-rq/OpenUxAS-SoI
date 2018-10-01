// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
* File:   MustFlyTaskService.h
* Author: colin
*
* Created on May 4, 2017
*/

#ifndef UXAS_SERVICE_TASK_MUST_FLY_TASK_SERVICE_H
#define UXAS_SERVICE_TASK_MUST_FLY_TASK_SERVICE_H

#include "UnitConversions.h"

#include "afrl/cmasi/MustFlyTask.h"
#include "uxas/messages/route/RouteRequest.h"

#include <cstdint> // int64_t
#include "TaskServiceBase.h"

namespace uxas
{
namespace service
{
namespace task
{

/*! \class c_Task_MustFlyTask
\brief A component that implements the CMASI MustFlyTask
*/

class MustFlyTaskService : public TaskServiceBase
{
public:

	static const std::string& s_typeName()
	{
		static std::string s_string("MustFlyTaskService");
		return (s_string);
	};

	static const std::vector<std::string> s_registryServiceTypeNames()
	{
		std::vector<std::string> registryServiceTypeNames = { s_typeName(), "afrl.cmasi.MustFlyTask", "afrl.famus.MustFlyTask" };
		return (registryServiceTypeNames);
	};

	static const std::string& s_directoryName()
	{
		static std::string s_string("");
		return (s_string);
	};

	static ServiceBase* create()
	{
		return new MustFlyTaskService;
	};

	MustFlyTaskService();
	virtual ~MustFlyTaskService();

	virtual void buildTaskPlanOptions() override;

private:

	static ServiceBase::CreationRegistrar<MustFlyTaskService> s_registrar;

	/** brief Copy construction not permitted */
	MustFlyTaskService(MustFlyTaskService const&) = delete;

	/** brief Copy assignment operation not permitted */
	void operator=(MustFlyTaskService const&) = delete;

	bool configureTask(const pugi::xml_node& serviceXmlNode) override;
	
	bool isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
                std::shared_ptr<TaskOptionClass>& taskOptionClass,
                int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route) override;

	bool isBuildAndSendImplementationRouteRequest(const int64_t& optionId,
        const std::shared_ptr<uxas::messages::task::TaskImplementationRequest>& taskImplementationRequest,
        const std::shared_ptr<uxas::messages::task::TaskOption>& taskOption) override;

	std::shared_ptr<afrl::cmasi::MustFlyTask> m_mustFlyTask;

};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_MUST_FLY_TASK_SERVICE_H */


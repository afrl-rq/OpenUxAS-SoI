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

				static const std::string&
					s_typeName()
				{
					static std::string s_string("MustFlyTaskService");
					return (s_string);
				};

				static const std::vector<std::string>
					s_registryServiceTypeNames()
				{
					std::vector<std::string> registryServiceTypeNames = { s_typeName(), "afrl.cmasi.MustFlyTask" };
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
					return new MustFlyTaskService;
				};

				MustFlyTaskService();

				virtual
					~MustFlyTaskService();

			private:

				static
					ServiceBase::CreationRegistrar<MustFlyTaskService> s_registrar;

				/** brief Copy construction not permitted */
				MustFlyTaskService(MustFlyTaskService const&) = delete;

				/** brief Copy assignment operation not permitted */
				void operator=(MustFlyTaskService const&) = delete;

			private:

				bool configureTask(const pugi::xml_node& serviceXmlNode) override;

				bool processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;


			public:
				const double m_defaultElevationLookAngle_rad = 60.0 * n_Const::c_Convert::dDegreesToRadians(); //60 deg down

			public: //virtual

				virtual void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) override;
				virtual void buildTaskPlanOptions() override;

			private:


				std::shared_ptr<afrl::cmasi::MustFlyTask> m_mustFlyTask;





			};

		}; //namespace task
	}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_MUST_FLY_TASK_SERVICE_H */


// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_TaskManager.h
 * Author: steve
 *
 * Created on August 31, 2015, 6:17 PM
 */

#ifndef UXAS_SERVICE_TASK_TASK_MANAGER_SERVICE_H
#define UXAS_SERVICE_TASK_TASK_MANAGER_SERVICE_H

#include "ServiceBase.h"

#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/impact/AreaOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/PointOfInterest.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "afrl/cmasi/OperatingRegion.h"
#include <set>
#include <cstdint> // int64_t


namespace uxas
{
namespace service
{
namespace task
{

/*! \class TaskManagerService
    \brief A service that constructs/destroys tasks.

 * 
 * Configuration String:
 *  <Service Type="TaskManagerService">
 *      <TaskOptions TaskType="uxas.project.pisr.PISR_Task"> <Option OptionName="AssignmentType" Value="MWRRP"/></TaskOptions>
 *  </Service>
 * 
 * Options:
 *  - TaskOptions entries provide options to tasks
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::RemoveTasks
 *  - afrl::cmasi::EntityState
 *  - afrl::cmasi::EntityConfiguration
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - afrl::vehicles::SurfaceVehicleConfiguration
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::vehicles::GroundVehicleState
 *  - afrl::vehicles::SurfaceVehicleState
 *  - afrl::cmasi::MissionCommand
 *  - afrl::cmasi::AutomationResponse
 *  - afrl::cmasi::FollowPathCommand
 *  - ALL TASKS
 * 
 * Sent Messages:
 *  - uxas::messages::uxnative::KillService
 *  - uxas::messages::uxnative::CreateNewService
 *  - afrl::cmasi::AutomationRequest
 *  - uxas::messages::task::UniqueAutomationRequest
 * 
 */

class TaskManagerService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("TaskManagerService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create() {
        return new TaskManagerService;
    };

    TaskManagerService();

    virtual
    ~TaskManagerService();

private:

    static
    ServiceBase::CreationRegistrar<TaskManagerService> s_registrar;

    /** brief Copy construction not permitted */
    TaskManagerService(TaskManagerService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(TaskManagerService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    //bool
    //initialize() override;

    //bool
    //start() override;

    //bool
    //terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

public:
    static std::string GetTaskStringIdFromId(const int64_t& taskId);

private:
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration> > m_idVsEntityConfiguration;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_idVsEntityState;
    std::unordered_map<int64_t, std::shared_ptr<afrl::impact::AreaOfInterest> > m_idVsAreaOfInterest;
    std::unordered_map<int64_t, std::shared_ptr<afrl::impact::LineOfInterest> > m_idVsLineOfInterest;
    std::unordered_map<int64_t, std::shared_ptr<afrl::impact::PointOfInterest> > m_idVsPointOfInterest;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::MissionCommand> > m_vehicleIdVsCurrentMission;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::KeepInZone> > m_idVsKeepInZone;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::KeepOutZone> > m_idVsKeepOutZone;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::OperatingRegion> > m_idVsOperatingRegion;
    /*! \brief container for managing task options read in from the XML configuration file.
     *  If there is no TaskId, then 0 is used. If there is no TaskType, then the string "NoTaskType" is used.
     * 
     * Based on the entries in the XML file the options will be passed to the tasks in the following manner:
     * - [Apply these options to the task of the given TaskId]
     * - [Apply these options to all tasks of the given TaskType]
     * - [Apply these options to all tasks] neither TaskID nor TaskType are given.*/
    std::unordered_map<int64_t, std::unordered_map<std::string, std::vector<std::string> > > m_TaskIdVsTaskTypeVsOptions;
    /*! \brief this maps task IDs to service IDs, used to create and kill services */
    std::unordered_map<int64_t,int64_t> m_TaskIdVsServiceId;
    /*! \brief this is the string used to index options with no TaskType */
	const std::string m_noTaskTypeString = std::string("NoTaskType");

    int64_t m_automationRequestId = 1000;

private:




};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_TASK_MANAGER_SERVICE_H */


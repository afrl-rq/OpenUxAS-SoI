// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_ImpactLineSearch.h
 * Author: steve
 *
 * Created on February 12, 2016, 6:17 PM
 */

#ifndef UXAS_SERVICE_TASK_IMPACT_LINE_SEARCH_TASK_SERVICE_H
#define UXAS_SERVICE_TASK_IMPACT_LINE_SEARCH_TASK_SERVICE_H

#include "TaskServiceBase.h"

#include "Dpss.h"    //from OHARA

#include "afrl/cmasi/LineSearchTask.h"

#include <cstdint> // int64_t
#include <unordered_map>

namespace uxas
{
namespace service
{
namespace task
{

/*! \class ImpactLineSearchTaskService
    \brief A component that implements a point search task.

        //AutomationRequest

        //For each eligible entity, calculate the
        //planning points required to calculate
        //task costs:
        //1) Request sensor footprint information
        //for all eligible vehicles (if required)

            
        // ->SensorFootprintRequest
        //SensorFootprintResponse
        
        //2) Find task options and composition.
        //3) For each option, calculate planning
        //points.

        // ->RouteRequest (cost only)
        //RouteResponse (cost only)

        //4) Send options and composition.
        
        // ->TaskPlanOptions
        //TaskImplementationRequest

        //1) Construct final plans
        //2) Cache assignment for use during
        //execution        
        
        // ->RouteRequest
        //RouteResponse
        // ->TaskImplementationResponse
        //AirVehicleState

        //Tasks monitor VehicleStates to act
        //on assigned portions of the plan,
        //e.g., starts recording video based
        //on vehicle state
 * 
 * Options:
 *  - LineSearchOneDirection
 * 
 * Subscribed Messages:
 *  - 
 * 
 * Sent Messages:
 *  - afrl::cmasi::VehicleActionCommand
 *  - uxas::messages::uxnative::VideoRecord
 * 
 * TASK: Subscribed Messages:
 *  - afrl::cmasi::EntityState
 *  - afrl::cmasi::EntityConfiguration
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::vehicles::GroundVehicleState
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - afrl::vehicles::SurfaceVehicleState
 *  - afrl::vehicles::SurfaceVehicleConfiguration
 *  - uxas::messages::task::UniqueAutomationRequest
 *  - uxas::messages::task::UniqueAutomationResponse
 *  - uxas::messages::route::RoutePlanResponse
 *  - uxas::messages::task::TaskImplementationRequest
 * 
 * TASK: Sent Messages:
 *  - uxas::messages::task::TaskInitialized
 *  - uxas::messages::task::TaskActive
 *  - uxas::messages::task::TaskComplete
 *  - uxas::messages::route::RoutePlanRequest
 *  - uxas::messages::task::TaskPlanOptions
 *  - uxas::messages::task::TaskImplementationResponse
 */


class ImpactLineSearchTaskService : public TaskServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("ImpactLineSearchTaskService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(), "afrl.impact.ImpactLineSearchTask"};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create() {
        return new ImpactLineSearchTaskService;
    };

    ImpactLineSearchTaskService();

    virtual
    ~ImpactLineSearchTaskService();

private:

    static
    ServiceBase::CreationRegistrar<ImpactLineSearchTaskService> s_registrar;

    /** brief Copy construction not permitted */
    ImpactLineSearchTaskService(ImpactLineSearchTaskService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(ImpactLineSearchTaskService const&) = delete;

    bool
    configureTask(const pugi::xml_node& serviceXmlNode) override;

public:
    const double m_defaultAzimuthLookAngle_rad = 10.0 * n_Const::c_Convert::dDegreesToRadians(); //10 deg
    const double m_defaultElevationLookAngle_rad = -60.0 * n_Const::c_Convert::dDegreesToRadians(); //-60 deg

public: //virtual
    virtual void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) override;
    virtual void buildTaskPlanOptions() override;
    virtual bool isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse, std::shared_ptr<TaskOptionClass>& taskOptionClass,
            int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route) override;

private:
    bool isCalculateOption(const int64_t& taskId, const std::vector<int64_t>& eligibleEntities,
            const double& nominalAltitude_m, const double& nominalSpeed_mps,
            const double& azimuthLookAngle_rad, const double& elevationLookAngle_rad,
            int64_t& optionId, std::string& algebraString); //NOTE:: optionId can be returned, changed


private:
    std::shared_ptr<afrl::cmasi::LineSearchTask> m_lineSearchTask;
    std::shared_ptr<afrl::impact::LineOfInterest> m_lineOfInterest;
    std::unordered_multimap<int64_t, std::shared_ptr<Dpss> > m_optionIdVsDpss;
    std::shared_ptr<Dpss> m_activeDpss;
    bool m_isPlanBothDirections = true;

public:


private:




};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_IMPACT_LINE_SEARCH_TASK_SERVICE_H */


// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   TemporalService.h
 * Author: derek
 *
 * Created on Aug 24, 2015, 9:31 AM
 */


#ifndef UXAS_SERVICE_AUTOMATION_LOGIC_CONTROLLER_H
#define UXAS_SERVICE_AUTOMATION_LOGIC_CONTROLLER_H

#include "ServiceBase.h"
#include "CallbackTimer.h"

#include "afrl/cmasi/OperatingRegion.h"
#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/AirVehicleState.h"

#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/AssignmentCostMatrix.h"
#include "uxas/messages/task/TaskPlanOptions.h"
#include "uxas/messages/task/TaskAssignment.h"
#ifdef AFRL_INTERNAL_ENABLED
#include "uxas/project/pisr/AssignmentType.h"
#endif

#include <memory>
#include <deque>
#include <unordered_map>
#include <unordered_set>

#include "Algebra.h"

namespace uxas
{
namespace service
{

/*! \class TemporalService
 *\brief Checks all elements of automation requests to make sure they are present 
 * before sending out a UniqueAutomationRequest. 
 * 
 * Configuration String: 
 *  <Service Type="TemporalService" MaxResponseTime_ms="5000"/>
 * 
 * Options:
 *  - MaxResponseTime_ms
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::AutomationRequest
 *  - afrl::impact::ImpactAutomationRequest
 *  - uxas::messages::task::UniqueAutomationResponse
 *  - uxas::messages::task::TaskAutomationRequest
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::impact::GroundVehicleConfiguration
 *  - afrl::impact::SurfaceVehicleConfiguration
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::impact::GroundVehicleState
 *  - afrl::impact::SurfaceVehicleState
 *  - afrl::cmasi::RemoveTasks
 *  - uxas::messages::task::TaskInitialized
 *  - afrl::cmasi::OperatingRegion
 *  - afrl::cmasi::KeepInZone
 *  - afrl::cmasi::KeepOutZone
 * 
 * Sent Messages:
 *  - uxas::messages::task::TaskAutomationResponse
 *  - afrl::cmasi::AutomationResponse
 *  - afrl::impact::ImpactAutomationResponse
 *  - uxas::messages::task::UniqueAutomationRequest
 *  - afrl::cmasi::ServiceStatus
 * 
 */


class TemporalService : public ServiceBase
{
public:

    std::string             remPAStr;
    int64_t                 mem_OperatingRegion;
    bool                    mem_RedoAllTasks;
    std::vector<int64_t>    mem_EntityList;
    std::vector<int64_t>    mem_TaskList;
    bool                    mem_LastIteration;
    bool                    mem_lastCompleted;
    std::vector<afrl::cmasi::MissionCommand*> mem_MissionCommandList;
    std::vector<int64_t>     endingLocationsEntityIDMissionList;
    std::vector<double>      endingLocationsLatPerMissionList;
    std::vector<double>      endingLocationsLonPerMissionList;
    std::vector<double>      endingLocationsAltPerMissionList;
    
    uxas::common::utilities::CAlgebra algebra; // ALGEBRA:: Algebra class definition

    static const std::string&
    s_typeName()
    {
        static std::string s_string("TemporalService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
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
        return new TemporalService;
    };

    TemporalService();

    virtual
    ~TemporalService();

private:
    protected: //virtual
class AssigmentPrerequisites
    {
    public:
        /** brief checks to make sure that all of the parameters 
         * required to generate an assignment are available. */
        bool isAssignmentReady(const bool& isUsingAssignmentTypes);
#ifdef AFRL_INTERNAL_ENABLED        
        void setAssignmentType(const uxas::project::pisr::AssignmentType::AssignmentType& assignmentType)
        {
            m_isNewAssignmentType = true;
            m_assignmentType = assignmentType;
        };
        uxas::project::pisr::AssignmentType::AssignmentType m_assignmentType;
#endif
    public:
        std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> m_uniqueAutomationRequest;
        std::shared_ptr<uxas::messages::task::AssignmentCostMatrix> m_assignmentCostMatrix;
        std::unordered_map<int64_t, std::shared_ptr < uxas::messages::task::TaskPlanOptions>> m_taskIdVsTaskPlanOptions;
        bool m_isNewAssignmentType{false};
    };

    static
    ServiceBase::CreationRegistrar<TemporalService> s_registrar;

    /** brief Copy construction not permitted */
    TemporalService(TemporalService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(TemporalService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    //bool
    //start() override;

    //bool
    //terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

    ////////////////////////
    // TIMER CALLBACKS
    /*! \brief this function gets called when the response timer expires */
    void calculateTiming();
    void SendTemporalRequest();
    void OnResponseTimeout();
    
    bool isCheckAutomationRequestRequirements(const std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>& uniqueAutomationRequest);
    void checkToSendNextRequest();
    
    /*! \brief  this timer is used to track time for the system to respond
     * to automation requests*/
    uint64_t m_responseTimerId{0};
    /*! \brief  parameter indicating the maximum time to wait for a response (in ms)*/
    uint32_t m_maxResponseTime_ms = {5000}; // default: 5000 ms

    enum AutomationRequestType
    {
        AUTOMATION_REQUEST,
        SANDBOX_AUTOMATION_REQUEST,
        TASK_AUTOMATION_REQUEST
    };
    
    // storage
    std::deque< std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> > m_waitingRequests;
    std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> m_waitingForResponse;
    bool m_isAllClear{true};
    std::unordered_map<int64_t, AutomationRequestType> m_sandboxMap;
    std::unordered_map<int64_t, int64_t> m_playId;
    std::unordered_map<int64_t, int64_t> m_solnId;
    
    std::unordered_map<int64_t,std::shared_ptr<afrl::cmasi::AirVehicleState>> m_vehicleStates;
    std::unordered_map<int64_t,double> m_timeAdjustment;

    std::unordered_set<int64_t> m_availableConfigurationEntityIds;
    std::unordered_set<int64_t> m_availableStateEntityIds;
    std::unordered_set<int64_t> m_availableKeepInZoneIds;
    std::unordered_set<int64_t> m_availableKeepOutZoneIds;
    std::unordered_set<int64_t> m_availableAreaOfInterestIds;
    std::unordered_set<int64_t> m_availableLineOfInterestIds;
    std::unordered_set<int64_t> m_availablePointOfInterestIds;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::OperatingRegion> > m_availableOperatingRegions;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::Task> > m_availableTasks;
    std::unordered_set<int64_t> m_availableStartedTaskIds;
    
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_AUTOMATION_REQUEST_VALIDATOR_SERVICE_H */

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_PlanBuilder.h
 * Author: steve
 *
 * Created on September 14, 2015, 6:17 PM
 */

#ifndef UXAS_SERVICE_PLAN_BUILDER_SERVICE_H
#define UXAS_SERVICE_PLAN_BUILDER_SERVICE_H

#include "ServiceBase.h"

#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"
#include "uxas/messages/task/TaskAssignmentSummary.h"
#include "uxas/messages/task/TaskAssignment.h"
#include "uxas/messages/task/TaskImplementationRequest.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/PlanningState.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/GimbalState.h"
#include "afrl/cmasi/GimbalAngleAction.h"
#include "afrl/impact/SpeedAltPair.h"
#include <afrl/cmasi/LoiterAction.h>
#include <afrl/impact/ImpactAutomationRequest.h>
#include <afrl/impact/ImpactAutomationResponse.h>

#include <cstdint> // int64_t
#include <deque>
#include <unordered_map>
#include <list>
namespace uxas
{
namespace service
{

/*! \class PlanBuilderService
    \brief A component that constructs plans from assignments.


 * 1) For each assigned task option, in order, request calculation of final waypoint plan 
 * 2) Construct resulting waypoint plans and send automation response.
 * 
 * MESSAGES:
 * ==> TaskAssignmentSummary
 * 
 * FOR EVERY TASK
 * <== TaskImplementationRequest
 * ==> TaskImplementationResponse
 * 
 * <== AutomationResponse
 * 
 * 
 * Configuration String: 
 *  <Service Type="PlanBuilderService" AssignmentStartPointLead_m="50.0" />
 * 
 * Options:
 *  - AssignmentStartPointLead_m
 * 
 * Subscribed Messages:
 *  - uxas::messages::task::UniqueAutomationRequest
 *  - uxas::messages::task::TaskAssignmentSummary
 *  - uxas::messages::task::TaskImplementationResponse
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::vehicles::GroundVehicleState
 *  - afrl::vehicles::SurfaceVehicleState
 * 
 * Sent Messages:
 *  - afrl::cmasi::ServiceStatus
 *  - uxas::messages::task::TaskImplementationRequest
 *  - uxas::messages::task::UniqueAutomationResponse
 * 
 */

class PlanBuilderService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("PlanBuilderService");
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
        return new PlanBuilderService;
    };

    PlanBuilderService();

    virtual
    ~PlanBuilderService();

private:

    static
    ServiceBase::CreationRegistrar<PlanBuilderService> s_registrar;

    /** brief Copy construction not permitted */
    PlanBuilderService(PlanBuilderService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(PlanBuilderService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;
    
    void processTaskAssignmentSummary(const std::shared_ptr<uxas::messages::task::TaskAssignmentSummary>& taskAssignmentSummary);
    void processTaskImplementationResponse(const std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse);
    void sendError(std::string& errMsg);
    
    bool sendNextTaskImplementationRequest(int64_t uniqueRequestID);
    void checkNextTaskImplementationRequest(int64_t uniqueRequestID);
    void AddLoitersToMissionCommands(std::shared_ptr<uxas::messages::task::UniqueAutomationResponse> response);
    /*! \brief  nested class for tracking projected state of an entity during the plan building process */
    class ProjectedState {
    public:
        ProjectedState() {};
        ~ProjectedState() { if(state) delete state; };
        void setState(uxas::messages::task::PlanningState* newState) {
            if(state) delete state;
            state = newState;
        };
        uxas::messages::task::PlanningState* state{nullptr};
        int64_t finalWaypointID{0};
        int64_t time{0}; // ms since 1 Jan 1970
    };

    /*! \brief  unique automation requests with key of corresponding unique automation request ID */
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> > m_uniqueAutomationRequests;
    
    /*! \brief  in progress build of unique automation response with key of corresponding unique automation request ID */
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::task::UniqueAutomationResponse> > m_inProgressResponse;
    
    /*! \brief  task assignment summaries with key of corresponding unique automation request ID */
    std::unordered_map<int64_t, std::shared_ptr<uxas::messages::task::TaskAssignmentSummary> > m_assignmentSummaries;
    
    /*! \brief  projected entity states with key of corresponding unique automation request ID */
    std::unordered_map< int64_t, std::vector< std::shared_ptr<ProjectedState> > > m_projectedEntityStates;
    
    /*! \brief  Track which task assignments have yet to be completed with key of corresponding unique automation request ID */
    std::unordered_map< int64_t, std::deque< std::shared_ptr<uxas::messages::task::TaskAssignment> > > m_remainingAssignments;
    
    /*! \brief  When in the 'busy' state, the key of the currently pending task implementation request ID
     *          mapped to the unique automation request ID (backwards from normal for easy look-up) */
    std::unordered_map< int64_t, int64_t > m_expectedResponseID;
    
    /*! \brief  latest entity states (used to get starting heading, position, and time) with key of entity ID */
    std::unordered_map< int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_currentEntityStates;

    std::unordered_map< int64_t, std::list<std::shared_ptr<afrl::impact::SpeedAltPair>>> m_reqeustIDVsOverrides;

    /*! \brief  this stores the next unique ID to be used when requesting task
     *          implementations. Incremented by one after use. */
    int64_t m_taskImplementationId{1};

    /*! \brief  this stores the next unique ID to be used when building a 
     *          waypoint list. Incremented by one after use. */
    int64_t m_commandId{1};

    /*! \brief  this is the distance to add to the position of the vehicle, in the
     * direction that the vehicle is headed, to calculate the starting point for 
     * new plans. Can be changed in XML configuration. */
    double m_assignmentStartPointLead_m{50.0};

    /*! \brief define end behavior for missions to prevent chaotic flight paths.*/
    bool m_addLoiterToEndOfMission = false;

    double m_deafultLoiterRadius{ 300.0 };

    /*! \brief  the turn type to send out in mission commands*/
    afrl::cmasi::TurnType::TurnType m_turnType = {afrl::cmasi::TurnType::TurnShort};
    bool m_overrideTurnType{false};
};





}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_PLAN_BUILDER_SERVICE_H */

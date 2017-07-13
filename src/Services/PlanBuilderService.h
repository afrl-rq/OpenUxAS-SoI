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
#include "uxas/messages/task/TaskAssignmentSummary.h"
#include "uxas/messages/task/TaskImplementationRequest.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RouteResponse.h"
#include "afrl/cmasi/EntityState.h"

#include <cstdint> // int64_t
#include <deque>

// Rust prototypes
extern "C" {
void* plan_builder_new();
void plan_builder_delete(void* raw_pb);
void* plan_builder_configure(void* raw_pb, double assignment_start_point_lead_m);
void plan_builder_process_received_lmcp_message(void* raw_pb, uint8_t *msg_buf, uint32_t msg_len);
}

namespace uxas
{
namespace service
{

///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////


/*! \class PlanBuilderService
    \brief A component that constructs plans from assignments.


 * 1) For each assigned task option,calculate final task plan. 
 * 2) Based on assigned order of task options, calculate final route plans, for
 * each entity, to execute assigned tasks. 
 * 3) Construct waypoint plans and send automation response.
 * 
 * MESSAGES:
 * ==> TaskAssignmentSummary
 * 
 * FOR EVERY TASK
 * <== TaskImplementationRequest
 * ==> TaskImplementationResponse
 * <== RouteRequest
 * ==> RouteResponse
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
 *  - afrl::impact::GroundVehicleState
 *  - afrl::impact::SurfaceVehicleState
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
    initialize() override;

    //bool
    //start() override;

    //bool
    //terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


public:
    int64_t m_startingWaypointID{100000000};

public:




public: //virtual





public:
private:
    void processTaskAssignmentSummary(const std::shared_ptr<uxas::messages::task::TaskAssignmentSummary>& taskAssignmentSummary);
    void processTaskImplementationResponse(const std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse);
    void buildAndSendThePlan();

    int64_t getNextImplementationId() {
        m_taskImplementationId++;
        return (m_taskImplementationId);
    };

    int64_t getStartingWaypointId() {
        return (m_startingWaypointID * m_taskImplementationId);
    };

    int64_t getNextCommandId() {
        m_commandId++;
        return (m_commandId);
    };


private:

    /*! \brief  this is the current automation request*/
    std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> m_uniqueAutomationRequest;

    /*! \brief  container to store entity states. (used to get starting heading, position, and time)*/
    std::unordered_map< int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_entityIdVsEntityState;

    /*! \brief  when a TaskAssignmentSummary messages is received, TaskImplementationRequest
     *  are constructed and stored in this container until they are ready to be sent out */
    std::unordered_map< int64_t, std::shared_ptr<std::deque<std::shared_ptr<uxas::messages::task::TaskImplementationRequest> > > > m_entityIdVsTaskImplementationRequests;

    /*! \brief  as they are received the TaskImplementationResponse messages
     * are used determine if new TaskImplementationRequest should be sent. The
     * TaskImplementationResponse messages are then stored in this container
     * until it is time to construct the automationresponse. */
    std::unordered_map< int64_t, std::shared_ptr<std::deque<std::shared_ptr<uxas::messages::task::TaskImplementationResponse> > > > m_entityIdVsTaskImplementationResponses;

    /*! \brief  this stores the last TaskImplementationId (and StartingWaypointId)
     sent out. It is incremented by 1 for each new ID. It is reset to zero each
     time a new TaskAssignmentSummary is received. */
    int64_t m_taskImplementationId{0};

    /*! \brief  CommandId used in the last mission command. Incremented by one
    * for each new mission command. Assume this id will be unique during the
     * lifetime run of the PlanBuilder*/
    int64_t m_commandId{0};

    /*! \brief  this is the distance to add to the position of the vehicle, in the
     * direction that the vehicle is headed, to calculate the starting point for 
     * new plans. */
    double m_assignmentStartPointLead_m{50.0};

    /*! \brief  the state of the Rust implementation of PlanBuilder */
    void* m_PlanBuilder;

private:




};





}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_PLAN_BUILDER_SERVICE_H */

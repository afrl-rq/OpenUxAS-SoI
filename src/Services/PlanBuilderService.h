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

#include <cstdint> // int64_t
#include <deque>
#include <unordered_map>

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

    /*! \brief  the state of the Rust implementation of PlanBuilder */
    void* m_PlanBuilder;
};





}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_PLAN_BUILDER_SERVICE_H */

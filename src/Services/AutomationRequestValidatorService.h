// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   AutomationRequestValidatorService.h
 * Author: derek
 *
 * Created on Aug 24, 2015, 9:31 AM
 */


#ifndef UXAS_SERVICE_AUTOMATION_REQUEST_VALIDATOR_SERVICE_H
#define UXAS_SERVICE_AUTOMATION_REQUEST_VALIDATOR_SERVICE_H

#include "ServiceBase.h"
#include "CallbackTimer.h"

#include "afrl/cmasi/OperatingRegion.h"
#include "afrl/cmasi/Task.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"

#include <memory>
#include <deque>
#include <unordered_map>
#include <unordered_set>

namespace uxas
{
namespace service
{

/*! \class AutomationRequestValidatorService
 *\brief Checks all elements of automation requests to make sure they are present 
 * before sending out a UniqueAutomationRequest. 
 * 
 * Configuration String: 
 *  <Service Type="AutomationRequestValidatorService" MaxResponseTime_ms="5000"/>
 * 
 * Options:
 *  - MaxResponseTime_ms: waits for specified time before rejecting request and proceeding
 * 
 * Design: The objective of the Automation Request Validator is to ensure that a request
 *         can be fulfilled given the current state of received messages. For example,
 *         an Automation Request that includes a task that has not yet been defined. In 
 *         addition to checking for appropriately formed requests, the Automation Request
 *         Validator will abandon an attempt to fulfill a request if the system exceeds
 *         a pre-defined time threshold.
 * 
 * Details: To accommodate the case when tasks are defined and immediately followed by an
 *          automation request, a small grace period is needed to allow tasks to initialize
 *          themselves in preparation for the coming request. To accommodate this, the
 *          Automation Request Validator takes the following steps: (1) validate request; 
 *          (2) check that each requested task is initialized; (3) send unique automation
 *          request; (4) receive and publish response.
 * 
 *          If the request is valid, but tasks are not yet initialized, a timer is started
 *          waiting for 'MaxResponseTime_ms' which terminates the request and returns an
 *          error when it times out. When all relevant 'TaskInitialization' messages are
 *          received, then the timer is disabled and the unique automation request sent.
 * 
 *          After the unique automation request is sent, the timer is again enabled such
 *          that if 'MaxResponseTime_ms' elapses, the request will be abandoned and an
 *          error reported. The incorporation of the time-outs ensures that in the event
 *          of a task initialization or assignment pipeline failure, the system can still
 *          respond to subsequent requests.
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::AutomationRequest
 *  - afrl::impact::ImpactAutomationRequest
 *  - uxas::messages::task::UniqueAutomationResponse
 *  - uxas::messages::task::TaskAutomationRequest
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - afrl::vehicles::SurfaceVehicleConfiguration
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::vehicles::GroundVehicleState
 *  - afrl::vehicles::SurfaceVehicleState
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


class AutomationRequestValidatorService : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("AutomationRequestValidatorService");
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
        return new AutomationRequestValidatorService;
    };

    AutomationRequestValidatorService();

    virtual
    ~AutomationRequestValidatorService();

private:

    static
    ServiceBase::CreationRegistrar<AutomationRequestValidatorService> s_registrar;

    /** brief Copy construction not permitted */
    AutomationRequestValidatorService(AutomationRequestValidatorService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(AutomationRequestValidatorService const&) = delete;

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
    void HandleAutomationRequest(std::shared_ptr<avtas::lmcp::Object>& autoRequest);
    void HandleAutomationResponse(std::shared_ptr<avtas::lmcp::Object>& autoResponse);
    void SendResponse(std::shared_ptr<uxas::messages::task::UniqueAutomationResponse>& resp);

    ////////////////////////
    // TIMER CALLBACKS
    /*! \brief this function gets called when the response timer expires */
    void OnResponseTimeout();
    /*! \brief this function gets called when the tasks involved have not reported initialization in time */
    void OnTasksReadyTimeout();
    
    bool isCheckAutomationRequestRequirements(const std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>& uniqueAutomationRequest);
    void checkTasksInitialized();
    void sendNextRequest();
    
    /*! \brief  this timer is used to track time for the system to respond to automation requests */
    uint64_t m_responseTimerId{0};
    /*! \brief  this timer is used to track time for the system to wait for task initialization */
    uint64_t m_taskInitTimerId{0};
    
    /*! \brief  parameter indicating the maximum time to wait for a response (in ms)*/
    uint32_t m_maxResponseTime_ms = {5000}; // default: 5000 ms

    enum AutomationRequestType
    {
        AUTOMATION_REQUEST,
        SANDBOX_AUTOMATION_REQUEST,
        TASK_AUTOMATION_REQUEST
    };
    
    /*! \brief  data structure for tracking request type and associated play/solution IDs */
    struct RequestDetails {
        AutomationRequestType requestType{AUTOMATION_REQUEST};
        int64_t playId{0};
        int64_t solnId{0};
        int64_t taskRequestId{0};
    };
    
    // storage
    std::deque< std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> > m_pendingRequests;
    std::deque< std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> > m_requestsWaitingForTasks;
    std::shared_ptr<uxas::messages::task::UniqueAutomationResponse> m_errorResponse;
    
    std::unordered_map<int64_t, RequestDetails> m_sandboxMap;
    
    std::unordered_set<int64_t> m_availableConfigurationEntityIds;
    std::unordered_set<int64_t> m_availableStateEntityIds;
    std::unordered_set<int64_t> m_availableKeepInZoneIds;
    std::unordered_set<int64_t> m_availableKeepOutZoneIds;
    std::unordered_set<int64_t> m_availableAreaOfInterestIds;
    std::unordered_set<int64_t> m_availableLineOfInterestIds;
    std::unordered_set<int64_t> m_availablePointOfInterestIds;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::OperatingRegion> > m_availableOperatingRegions;
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::Task> > m_availableTasks;
    std::unordered_set<int64_t> m_availableInitializedTasks;
    
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_AUTOMATION_REQUEST_VALIDATOR_SERVICE_H */

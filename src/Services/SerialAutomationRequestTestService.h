// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_SerialAutomationRequest.h
 * Author: derek
 *
 * Created on Aug 24, 2015, 9:31 AM
 */



#ifndef UXAS_SERVICE_TEST_SERIAL_AUTOMATION_REQUEST_TEST_SERVICE_H
#define UXAS_SERVICE_TEST_SERIAL_AUTOMATION_REQUEST_TEST_SERVICE_H

#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "afrl/cmasi/CMASI.h"
#include "afrl/impact/IMPACT.h"

#include <memory>
#include <deque>

namespace uxas
{
namespace service
{
namespace test
{

   
/*! \class SerialAutomationRequestTestService
        \brief A component that only forwards 'AutomationRequests' and
        'SandboxAutomationRequests' when the previous has been answered
 * 
 * Configuration String: 
 * 
 * Options:
 *  - 
 * 
 * Subscribed Messages:
 *  - 
 * 
 * Sent Messages:
 *  - 
 * 
 */

class SerialAutomationRequestTestService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("SerialAutomationRequestTestService"); return (s_string); };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() { static std::string s_string(""); return (s_string); };

    static ServiceBase*
    create() { return new SerialAutomationRequestTestService; };

    SerialAutomationRequestTestService();

    virtual
    ~SerialAutomationRequestTestService();

private:

    static
    ServiceBase::CreationRegistrar<SerialAutomationRequestTestService> s_registrar;

    /** brief Copy construction not permitted */
    SerialAutomationRequestTestService(SerialAutomationRequestTestService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(SerialAutomationRequestTestService const&) = delete;

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




    public: //virtual






        ////////////////////////
        // TIMER CALLBACKS
        /*! \brief this function gets called when the response timer expires */
        void OnResponseTimeout();

    private:




        /*! \brief  this timer is used to track time for the system to respond
        * to automation requests*/
        uint64_t m_responseTimerId{ 0 };
        /*! \brief  parameter indicating the maximum time to wait for a response (in ms)*/
        uint32_t m_maxResponseTime_ms = { 300 }; // default: 300 ms
        
        // storage
        std::deque< std::shared_ptr<avtas::lmcp::Object> > m_waitingRequests;
        bool m_isAllClear{ true };
    };

}; //namespace test
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TEST_SERIAL_AUTOMATION_REQUEST_TEST_SERVICE_H */

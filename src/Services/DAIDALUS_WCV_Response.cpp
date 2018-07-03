// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   DAIDALUS_WCV_Response.cpp
 * Author: SeanR
 *
 * Created on June 30 2018
 * 
 * 
 */

// include header for this service
#include "larcfm/DAIDALUS/DAIDALUSConfiguration.h"
#include "larcfm/DAIDALUS/WellClearViolationIntervals.h"
#include "DAIDALUS_WCV_Response.h"

#include <cmath>
#include <vector>
#include <iostream>     // std::cout, cerr, etc

// convenience definitions for the option strings
#define STRING_XML_OPTION_STRING "OptionString"
#define STRING_XML_OPTION_INT "OptionInt"

// namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{

// this entry registers the service in the service creation registry
DAIDALUS_WCV_Response::ServiceBase::CreationRegistrar<DAIDALUS_WCV_Response>
DAIDALUS_WCV_Response::s_registrar(DAIDALUS_WCV_Response::s_registryServiceTypeNames());

// service constructor
DAIDALUS_WCV_Response::DAIDALUS_WCV_Response()
: ServiceBase(DAIDALUS_WCV_Response::s_typeName(), DAIDALUS_WCV_Response::s_directoryName()) { };

// service destructor
DAIDALUS_WCV_Response::~DAIDALUS_WCV_Response() { };


bool DAIDALUS_WCV_Response::configure(const pugi::xml_node& ndComponent)
{
    bool isSuccess(true);

 
    // subscribe to messages::
    addSubscriptionAddress(larcfm::DAIDALUS::WellClearViolationIntervals::Subscription);
    addSubscriptionAddress(larcfm::DAIDALUS::DAIDALUSConfiguration::Subscription);

    return (isSuccess);
}

bool DAIDALUS_WCV_Response::initialize()
{
    // perform any required initialization before the service is started
    
    return (true);
}

bool DAIDALUS_WCV_Response::start()
{
    // perform any actions required at the time the service starts
    
    return (true);
};

bool DAIDALUS_WCV_Response::terminate()
{
    // perform any action required during service termination, before destructor is called.
    
    return (true);
}

bool DAIDALUS_WCV_Response::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    if (larcfm::DAIDALUS::isDAIDALUSConfiguration(receivedLmcpMessage->m_object))
    {
        
    }
    return false;
}

}; //namespace service
}; //namespace uxas

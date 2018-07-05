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
    //TODO: Add configuration handling to determine which mode of response to use, i.e. heading/track, horizontal speed, vertical speed, or altitude 
    
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
        std::shared_ptr<larcfm::DAIDALUS::DAIDALUSConfiguration> configuration = 
                std::static_pointer_cast<larcfm::DAIDALUS::DAIDALUSConfiguration>(receivedLmcpMessage->m_object);
        m_action_time_threshold_s = configuration->getAlertTime3();
        m_vertical_rate_mps = configuration->getVerticalRate();
        m_horizontal_accel_mpsps = configuration->getHorizontalAcceleration();
        m_vertical_accel_mpsps = configuration->getVerticalAcceleration();
        m_isReadyToAct = true;  //boolean to determine when ready to act; determined by having a threshold time set.
    }
    if (larcfm::DAIDALUS::isWellClearViolationIntervals(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals> WCVIntervals = 
                std::static_pointer_cast<larcfm::DAIDALUS::WellClearViolationIntervals> (receivedLmcpMessage->m_object);
        if (m_isReadyToAct)
        {
            for (size_t i = 0; i < WCVIntervals->getEntityList().size(); i++)
            {
                if (WCVIntervals->getTimeToViolationList()[i] <= m_action_time_threshold_s)
                {
                    m_ConflictResolutionList.push_back(WCVIntervals->getEntityList()[i]);
                }
            }
            if (!m_isConflict && m_ConflictResolutionList.size() > 0)
            {
                m_isConflict = true;//bool t = SetisConflict(true);
            }
            if (m_isConflict)
            {
                uint32_t RoW = m_entityId;
                // determine the vehicle that has the Right of Way
                for (int i : m_ConflictResolutionList)
                //for (size_t i = m_ConflictResolutionList.cbegin();  i < m_ConflictResolutionList.size(); i++)
                {
                    if (m_ConflictResolutionList[i] < RoW)
                    {
                        RoW = m_ConflictResolutionList[i];
                    }                    
                }
                if (m_entityId == RoW)
                {
                    //Ownship has Right of Way and therefore should take no action 
                    m_isConflict = false;
                }
                else
                {
                    if (!m_isTakenAction)
                    {
                        //TODO: send vehicle action command
                        m_isTakenAction = true;
                    }
                    else
                    {
                        //TODO: hold conflict until elapsed time for maneuver has passed or until desired state attained
                        //TODO: Compare desired "mode value" to current nogo band and if outside mode value send action command to desired and set isConflict to false

                    }
                }
            }
        }
    }

    return false;
}
bool DAIDALUS_WCV_Response::SetisConflict(bool& val)
{
    //set m_isConflict to value passed in
    m_isConflict = val;
    return true;
}
} //namespace service
} //namespace uxas

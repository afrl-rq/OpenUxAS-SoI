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
//#include "stdUniquePtr.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/FlightDirectorAction.h"
#include "afrl/cmasi/GoToWaypointAction.h"
#include <algorithm>
#include <cmath>
#include <memory>
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
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
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
    if (afrl::cmasi::isAutomationResponse(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<afrl::cmasi::AutomationResponse> pAutoResponse = 
                std::static_pointer_cast<afrl::cmasi::AutomationResponse>(receivedLmcpMessage->m_object);
        for (uint32_t i = 0; i < pAutoResponse->getMissionCommandList().size(); i++)
        {
            if (pAutoResponse->getMissionCommandList()[i]->getVehicleID() == m_entityId)
            {
                m_MissionCommand = std::make_shared<afrl::cmasi::MissionCommand>(*(pAutoResponse->getMissionCommandList()[i]->clone()));    //why doesn't this cause memory leaks from not getting cleaned up?
                break;
            }
        }
        //m_MissionCommand = pAutoResponse->getMissionCommandList()[it_MyMissionCommand];
        //auto it_AutomationResponse = std::find_if(pAutoResponse->getMissionCommandList().cbegin(), pAutoResponse->getMissionCommandList().cend(), 
         //       [&] (const afrl::cmasi::MissionCommand* pMission){ return pMission->getVehicleID() == m_entityId; } );
                
                
        m_isReadyToActMissionCommand = true;
    }
    else if (afrl::cmasi::isMissionCommand(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<afrl::cmasi::MissionCommand> pMissionCommand = 
                std::static_pointer_cast<afrl::cmasi::MissionCommand>(receivedLmcpMessage->m_object);
        if (pMissionCommand->getVehicleID() == m_entityId)
        {
            m_MissionCommand = std::make_shared<afrl::cmasi::MissionCommand>(*(pMissionCommand->clone()));  //why doesn't this cause memory leaks from not getting cleaned up?
        }
        m_isReadyToActMissionCommand = true;
    }
    if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<afrl::cmasi::AirVehicleState> pAirVehicleState = 
                std::static_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpMessage->m_object);
        if (!m_isTakenAction)
        {
            m_NextWaypoint = pAirVehicleState->getCurrentWaypoint();
        }
        m_isReadyToActWaypoint = true;
    }
    if (larcfm::DAIDALUS::isDAIDALUSConfiguration(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<larcfm::DAIDALUS::DAIDALUSConfiguration> configuration = 
                std::static_pointer_cast<larcfm::DAIDALUS::DAIDALUSConfiguration>(receivedLmcpMessage->m_object);
        m_action_time_threshold_s = configuration->getAlertTime3();
        m_vertical_rate_mps = configuration->getVerticalRate();
        m_horizontal_accel_mpsps = configuration->getHorizontalAcceleration();
        m_vertical_accel_mpsps = configuration->getVerticalAcceleration();
        m_isReadyToActConfiguration = true;  //boolean indicating if a threshold time is set from reading a DAIDALUS configuration parameter.
    }
    if (larcfm::DAIDALUS::isWellClearViolationIntervals(receivedLmcpMessage->m_object))
    {
        if (m_isReadyToActWaypoint && m_isReadyToActMissionCommand && m_isReadyToActConfiguration)
        {
            m_isReadyToAct = true;  //boolean to determine when ready to act; by having a threshold time set, a desired waypoint, and a missioncommand waypoint list
        }
        std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals> pWCVIntervals = 
                std::static_pointer_cast<larcfm::DAIDALUS::WellClearViolationIntervals> (receivedLmcpMessage->m_object);
        if (m_isReadyToAct)
        {
            m_CurrentState.altitude_m = pWCVIntervals->getCurrentAltitude();
            m_CurrentState.heading_deg = pWCVIntervals->getCurrentHeading();
            m_CurrentState.horizontal_speed_mps = pWCVIntervals->getCurrentGoundSpeed();
            m_CurrentState.vertical_speed_mps = pWCVIntervals->getCurrentVerticalSpeed();
            m_CurrentState.latitude_deg = pWCVIntervals->getCurrentLatitude();
            m_CurrentState.longitude_deg = pWCVIntervals->getCurrentLongitude();
            for (size_t i = 0; i < pWCVIntervals->getEntityList().size(); i++)
            {
                if (pWCVIntervals->getTimeToViolationList()[i] <= m_action_time_threshold_s)
                {
                    m_ConflictResolutionList.push_back(pWCVIntervals->getEntityList()[i]);
                }
            }
            if (!m_isConflict && m_ConflictResolutionList.size() > 0)
            {
                m_isConflict = true;//bool t = SetisConflict(true);
            }
            if (m_isConflict)
            {
                //Get conflict bands
                
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
                    m_ConflictResolutionList.clear();   //Ownship is not in conflict, thus ConflictResolutionList should be cleared.
                }
                else
                {
                    if (!m_isTakenAction)
                    {
                        //TODO: Determine recommended action from DAIDALUS
                        //TODO: set action response to aforementioned recommended action
                        //TODO: send vehicle action command
                        //TODO: remove RoW vehicle from the ConflictResolutionList
                        std::unique_ptr<afrl::cmasi::FlightDirectorAction> pDivertThisWay;
                        pDivertThisWay->setHeading(m_CurrentState.heading_deg+90);
                        m_isTakenAction = true;
                    }
                    else
                    {
                        //TODO: hold conflict until elapsed time for maneuver has passed or until desired state attained
                        //TODO: Compare desired "mode value" to current nogo band and if outside mode value send action command to desired and set isConflict to false
                        //TODO: Evaluate the size of the ConflictResolutionList: if empty do nothing else, if empty and maneuver obtained, flag m_isTakenAction to false
                        //TODO: remove RoW vehicle from the ConflictResolutionList
                        

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

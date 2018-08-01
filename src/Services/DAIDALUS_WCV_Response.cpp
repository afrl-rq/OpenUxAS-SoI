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
#include "DAIDALUS_WCV_Response.h"
#include "larcfm/DAIDALUS/DAIDALUSConfiguration.h"
#include "larcfm/DAIDALUS/WellClearViolationIntervals.h"
#include "FlatEarth.h"
#include "Util.h"
#include "stdUniquePtr.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/FlightDirectorAction.h"
#include "afrl/cmasi/CommandStatusType.h"
#include "afrl/cmasi/GoToWaypointAction.h"
#include "afrl/cmasi/MissionCommand.h"
#include "Constants/Convert.h"


#include <algorithm>
#include <cmath>
#include <memory>
#include <cstdint>
#include <vector>
#include <iostream>     // std::cout, cerr, etc

// convenience definitions for the option strings
#define STRING_XML_OPTION_STRING "OptionString"
#define STRING_XML_OPTION_INT "OptionInt"

#define MILLISECONDSTOSECONDS  1.0/1000.0;
namespace
{
    bool isInRange (const double lower, const double upper, const double value)
    {
        return ((lower <= value) && (value <= upper));
    }
    
}

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

    //TODO: Allow class member variables to be set via xml-- Maneuver type, time thresholds, maneuver offsets from NEAR interval, etc... 
    //TODO: Allow for multiple Response services to be active by using vehicleID passed in via xml in place of m_entityId.
    // subscribe to messages::
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(larcfm::DAIDALUS::WellClearViolationIntervals::Subscription);
    addSubscriptionAddress(larcfm::DAIDALUS::DAIDALUSConfiguration::Subscription);

    return (isSuccess);
}

/*bool isRoW(const int64_t ID)
{
    return (ID == m_RoW);
}*/

void DAIDALUS_WCV_Response::ResetResponse()
{
    m_isTakenAction = false;
    m_isActionCompleted = false;
    m_isConflict = false;
    m_ConflictResolutionList.clear();
}
bool DAIDALUS_WCV_Response::isWithinTolerance()
{
    //TODO: extend function to be passed the type of divert maneuver and consider altitude, ground speed, and vertical speed.
    if (std::abs((m_DivertState.heading_deg - m_CurrentState.heading_deg)) <= m_heading_tolerance_deg)
    {
        if (!m_isCloseToDesired)
        {
            m_tolerance_clock_s = m_CurrentState.time_s;
        }
        m_isCloseToDesired = true;
    }
    else
    {
        m_isCloseToDesired = false;
    }
    if ((m_CurrentState.time_s - m_tolerance_clock_s) >= m_tolerance_threshold_time_s)
    {
        std::cout << "Within Tolerance" << std::endl;
        return true;
    }
    else
    {
        std::cout << "Not within tolerance" << std::endl;
        return false;
    }
}

bool DAIDALUS_WCV_Response::isSafeToReturnToMission(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals> DAIDALUS_bands)
{
    //TODO:  accept maneuver type as a parameter and consider safe to return for altitude, ground speed, and vertical speed maneuvers.
    //std::cout << "Inside isSafe" << std::endl;
    uxas::common::utilities::FlatEarth flatEarth;
    //std::cout << "after flat" << std::endl;
    double CS_North_m, CS_East_m, WP_North_m, WP_East_m;
    double WP_latitude_deg, WP_longitude_deg ;
    //for (uint i = 0; i < m_MissionCommand->getWaypointList().size(); i++)
    if (m_MissionCommand == nullptr)
    {
        return true;
    }
    else 
    {
        for (auto i : m_MissionCommand->getWaypointList())
        {
            //std::cout << "Inside loop" << std::endl;
            if (i->getNumber() == m_NextWaypoint)
            {
                //std::cout << "I found a waypoint in order to return to mission" << std::endl;
                WP_latitude_deg = i->getLatitude();
                WP_longitude_deg = i->getLongitude();
                m_ReturnState.altitude_m = i->getAltitude();
                m_ReturnState.horizontal_speed_mps = i->getSpeed();
                m_ReturnState.vertical_speed_mps = i->getClimbRate();
                break;
            }
        }
        //std::cout << "After the fall" << std::endl;
        flatEarth.ConvertLatLong_degToNorthEast_m(m_CurrentState.latitude_deg, m_CurrentState.longitude_deg, CS_North_m, CS_East_m);
        //std::cout << "First flat earth worked." << std::endl;
        flatEarth.ConvertLatLong_degToNorthEast_m(WP_latitude_deg, WP_longitude_deg, WP_North_m, WP_East_m);
        m_ReturnState.heading_deg = std::fmod((n_Const::c_Convert::dRadiansToDegrees()*std::atan2((WP_East_m - CS_East_m), (WP_North_m - CS_North_m))) + 360.0, 360.0);
        std::cout << "The computed heading necessary to return to mission is " << m_ReturnState.heading_deg << " degrees." << std::endl;
        struct intervals
        {
            double upper;

            double lower;
        };
        std::vector<intervals> bands;
        intervals temp;
        for (uint i = 0; i < DAIDALUS_bands->getWCVGroundHeadingIntervals().size(); i++)
            {
                temp.lower = std::fmod(DAIDALUS_bands->getWCVGroundHeadingIntervals()[i]->getGroundHeadings()[0]+360.0, 360.0);
                temp.upper = std::fmod(DAIDALUS_bands->getWCVGroundHeadingIntervals()[i]->getGroundHeadings()[1]+360.0, 360.0);
                bands.push_back(temp);
            }
        uint initial_band = UINT32_MAX;  //band that the Return to Mission heading was in.
        bool isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
        for (uint i = 0; i < bands.size(); i++)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_ReturnState.heading_deg))
            {
                initial_band = i;
                isFound = true;
                break;
            }
        }
        if (initial_band == UINT32_MAX)
        {
            return true;
        }
        else if (isFound && DAIDALUS_bands->getWCVGroundHeadingRegions()[initial_band] == larcfm::DAIDALUS::BandsRegion::NEAR)
        {
            std::cout << "NOT SAFE TO RETURN TO MISSION" << std::endl;
            std::cout << std::endl;
            return false;
        }
        else
        {
            return true;
        }
    }
    //TODO: form return state heading ..--done
    //TODO: check if return state is in a near band... if so not safe to return--done
    //TODO: check if return state must pass through a near band to get there from current state and determine appropriate action
    //return true;
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
    //Process automation responses to retain a copy of the mission command--Mission commands for non-ownship vehicles are ignored
    //Assumption that only one automation response expected...subsequent automation responses will lead to unintended behavior.
    if (afrl::cmasi::isAutomationResponse(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<afrl::cmasi::AutomationResponse> pAutoResponse = 
                std::static_pointer_cast<afrl::cmasi::AutomationResponse>(receivedLmcpMessage->m_object);
        for (uint32_t i = 0; i < pAutoResponse->getMissionCommandList().size(); i++)
        {
            if (pAutoResponse->getMissionCommandList()[i]->getVehicleID() == m_entityId)
            {
                m_MissionCommand = std::make_shared<afrl::cmasi::MissionCommand>(*(pAutoResponse->getMissionCommandList()[i]->clone()));    //why doesn't this cause memory leaks from not getting cleaned up?
                m_isOnMission = true;
                break;
            }
            else 
            {
                m_MissionCommand = nullptr;
                m_isOnMission = false;
            }
        }
        //m_MissionCommand = pAutoResponse->getMissionCommandList()[it_MyMissionCommand];
        //auto it_AutomationResponse = std::find_if(pAutoResponse->getMissionCommandList().cbegin(), pAutoResponse->getMissionCommandList().cend(), 
         //       [&] (const afrl::cmasi::MissionCommand* pMission){ return pMission->getVehicleID() == m_entityId; } );
                
        //std::cout << "Response has Mission Command from Automation Response" << std::endl;        
        m_isReadyToActMissionCommand = true;
    }
    else if (afrl::cmasi::isMissionCommand(receivedLmcpMessage->m_object))
    {
        //Process mission commands to retain a copy of the mission command--Mission commands for non-ownship vehicles are ignored
        //Assumption that only one mission command message expected...subsequent mission commands will lead to unintended behavior.
        std::shared_ptr<afrl::cmasi::MissionCommand> pMissionCommand = 
                std::static_pointer_cast<afrl::cmasi::MissionCommand>(receivedLmcpMessage->m_object);
        if (pMissionCommand->getVehicleID() == m_entityId)
        {
            m_MissionCommand = std::make_shared<afrl::cmasi::MissionCommand>(*(pMissionCommand->clone()));  //why doesn't this cause memory leaks from not getting cleaned up?
            m_isOnMission = true;
        }
        else 
        {
            m_MissionCommand = nullptr;
            m_isOnMission = false;
        }
        m_isReadyToActMissionCommand = true;
    }
    if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<afrl::cmasi::AirVehicleState> pAirVehicleState = 
                std::static_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpMessage->m_object);
        if (pAirVehicleState->getID() == m_entityId)
        {
            m_CurrentState.altitude_m = pAirVehicleState->getLocation()->getAltitude();
            m_CurrentState.heading_deg = std::fmod(pAirVehicleState->getCourse()+360.0,360.0); //Course reported between -180 and 180 deg
            m_CurrentState.horizontal_speed_mps = pAirVehicleState->getGroundspeed();
            m_CurrentState.vertical_speed_mps = pAirVehicleState->getVerticalSpeed();
            m_CurrentState.latitude_deg = pAirVehicleState->getLocation()->getLatitude();
            m_CurrentState.longitude_deg = pAirVehicleState->getLocation()->getLongitude();
            m_CurrentState.altitude_type = pAirVehicleState->getLocation()->getAltitudeType();
            m_CurrentState.speed_type = afrl::cmasi::SpeedType::Groundspeed;
            m_CurrentState.time_s = pAirVehicleState->getTime()*MILLISECONDSTOSECONDS;
            if (m_isOnMission)
            {
                m_NextWaypoint = pAirVehicleState->getCurrentWaypoint();
                m_isReadyToActWaypoint = true;
                //std::cout << "DAIDALUS Response has the next waypoint" << std::endl;
            }
        }
    }
    if (larcfm::DAIDALUS::isDAIDALUSConfiguration(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<larcfm::DAIDALUS::DAIDALUSConfiguration> configuration = 
                std::static_pointer_cast<larcfm::DAIDALUS::DAIDALUSConfiguration>(receivedLmcpMessage->m_object);
        m_action_time_threshold_s = configuration->getAlertTime3();
        m_vertical_rate_mps = configuration->getVerticalRate();
        m_horizontal_accel_mpsps = configuration->getHorizontalAcceleration();
        m_vertical_accel_mpsps = configuration->getVerticalAcceleration();
        m_turn_rate_degps = configuration->getTurnRate();
        m_isReadyToActConfiguration = true;  //boolean indicating if a threshold time is set from reading a DAIDALUS configuration parameter.
        //std::cout << "DAIDALUS Response has received the DAIDALUS configuration used for detection." << std::endl;
    }
    if (larcfm::DAIDALUS::isWellClearViolationIntervals(receivedLmcpMessage->m_object))
    {
        //std::cout << "DAIDALUS Response has received a violation message." << std::endl;
        //if (m_isReadyToActWaypoint && m_isReadyToActMissionCommand && m_isReadyToActConfiguration)
        if (m_isReadyToActMissionCommand && m_isReadyToActConfiguration)
        {
            m_isReadyToAct = true;  //boolean to determine when ready to act; by having a threshold time set, a desired waypoint, and a missioncommand waypoint list
        }
        std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals> pWCVIntervals = 
                std::static_pointer_cast<larcfm::DAIDALUS::WellClearViolationIntervals> (receivedLmcpMessage->m_object);
        if (m_isReadyToAct)
        {
            /*
            m_CurrentState.altitude_m = pWCVIntervals->getCurrentAltitude();
            m_CurrentState.heading_deg = pWCVIntervals->getCurrentHeading();
            m_CurrentState.horizontal_speed_mps = pWCVIntervals->getCurrentGoundSpeed();
            m_CurrentState.vertical_speed_mps = pWCVIntervals->getCurrentVerticalSpeed();
            m_CurrentState.latitude_deg = pWCVIntervals->getCurrentLatitude();
            m_CurrentState.longitude_deg = pWCVIntervals->getCurrentLongitude();
             * */
            //std::cout << "DAIDALUS Response has received a violation message and is ready to act on it" << std::endl;
            if (!m_isConflict)
            {
                for (size_t i = 0; i < pWCVIntervals->getEntityList().size(); i++)
                {
                    if (pWCVIntervals->getTimeToViolationList()[i] <= m_action_time_threshold_s)
                    {
                        std::cout << "Adding " << pWCVIntervals->getEntityList()[i] << " to the Conflict Resolution List" << std::endl;
                        m_ConflictResolutionList.push_back(pWCVIntervals->getEntityList()[i]);
                    }
                }
            }    
            if (!m_isConflict && m_ConflictResolutionList.size() > 0) //TODO: add check for current heading in NEAR to conditional for action.
            {
                m_isConflict = true;//bool t = SetisConflict(true);
            }
            if (m_isConflict)
            {
                //TODO: Get conflict bands and store
                std::cout << "I HAVE DETERMINED THAT A CONFLICT MUST BE RESOLVED" << std::endl;
                if (m_ConflictResolutionList.size() > 0)
                {
                    m_RoW = INT64_MAX;
                }
                else
                {
                    m_RoW = INT64_MIN;
                }
                // determine the vehicle that has the Right of Way
                for (int64_t i : m_ConflictResolutionList)
                //for (size_t i = m_ConflictResolutionList.cbegin();  i < m_ConflictResolutionList.size(); i++)
                {
                    if (i < m_RoW)
                    {
                        m_RoW = i;
                    }                 
                    std::cout << "A Candidate for the Right of Way vehicle is Entity " << m_RoW << std::endl;
                }
                if (m_entityId < m_RoW)
                {
                    //Ownship has Right of Way and therefore should take no action 
                    ResetResponse();
                    std::cout << "I HAVE THE RIGHT OF WAY--NOT DOING ANYTHING TO AVOID COLLISION" << std::endl;
                }
                else
                {
                    //std::remove_if(m_ConflictResolutionList.begin(), m_ConflictResolutionList.end(), [&](int64_t ID) { return ID == m_RoW; });
                    std::vector<int64_t>::iterator expunge = std::find(m_ConflictResolutionList.begin(), m_ConflictResolutionList.end(), m_RoW);
                    
                    if (expunge != m_ConflictResolutionList.end())
                    {
                        std::cout << "Removing " << *expunge << " from Conflict Resolution List" << std::endl;
                        m_ConflictResolutionList.erase(expunge);
                    }
                    
                    /* for (auto ii = m_ConflictResolutionList.begin(); ii != m_ConflictResolutionList.end(); ii++)
                    //for (auto ii : m_ConflictResolutionList)
                    {                         
                        if (*ii == m_RoW)
                        {
                            //expunge = ii;
                            std::cout << "Removing " << *ii << " from Conflict Resolution List" << std::endl;
                            //m_ConflictResolutionList.erase(ii);
                            break;
                        }                        
                    } //*/
                    // m_ConflictResolutionList.erase(expunge);
                    if (!m_isTakenAction)
                    {
                        //Current logic assumes DAIDALUS returns bands intervals ordered and grouped from 0(True North) to 360
                        m_DivertState.heading_deg = m_CurrentState.heading_deg;
                        std::cout << "Current heading = " << m_CurrentState.heading_deg << std::endl;
                        struct intervals
                        {
                            double lower;
                            double upper;
                        };
                        std::vector<intervals> bands;
                        intervals temp;
                        for (uint i = 0; i < pWCVIntervals->getWCVGroundHeadingIntervals().size(); i++)
                        {
                            temp.lower = std::fmod(pWCVIntervals->getWCVGroundHeadingIntervals()[i]->getGroundHeadings()[0]+360.0, 360.0);
                            temp.upper = std::fmod(pWCVIntervals->getWCVGroundHeadingIntervals()[i]->getGroundHeadings()[1]+360.0, 360.0);
                            bands.push_back(temp);
                            std::cout << "Lower = " << temp.lower << std::endl;
                            std::cout << "Upper = " << temp.upper << std::endl;
                        }
                        std::cout << std::endl;
                        uint initial_band = 0;  //band that the initial heading was in.
                        bool isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
                        for (uint i = 0; i < bands.size(); i++)
                        {
                            if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.heading_deg))
                            {
                                m_DivertState.heading_deg = bands[i].upper + m_heading_interval_buffer_deg;
                                if (!isFound)
                                {
                                    initial_band = i;
                                    isFound = true;
                                }
                            }
                        }
                        if (m_DivertState.heading_deg > 360.0)  //If divert heading is greater than 360, a left turn is preferred.
                        {
                            for (uint i = initial_band; i > 0; i--)
                            {
                                if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.heading_deg))
                                {
                                    m_DivertState.heading_deg = bands[i].lower - m_heading_interval_buffer_deg;
                                }
                            }
                        }
                        if (m_DivertState.heading_deg < 0.0) //If after checking right turns and left turns no better heading found, keep current heading
                        {
                            m_DivertState.heading_deg = m_CurrentState.heading_deg;
                        }
                        //TODO: Determine recommended action from DAIDALUS
                        //TODO: set action response to aforementioned recommended action
                        //TODO: ensure divert action does not violate keep out zones
                        //TODO: send vehicle action command--done
                        //TODO: remove RoW vehicle from the ConflictResolutionList--done by nature of the loop
                        //m_DivertState.heading_deg = m_CurrentState.heading_deg + 90.0;  //make sure heading is from 0 to 360
                        std::cout << "Divert to heading " << m_DivertState.heading_deg << std::endl;
                        m_DivertState.altitude_m = m_CurrentState.altitude_m;
                        m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;
                        m_DivertState.vertical_speed_mps = m_CurrentState.vertical_speed_mps;                        
                        
                        std::unique_ptr<afrl::cmasi::FlightDirectorAction> pDivertThisWay = uxas::stduxas::make_unique<afrl::cmasi::FlightDirectorAction>();
                        pDivertThisWay->setHeading(static_cast<float>(m_DivertState.heading_deg)); 
                        pDivertThisWay->setAltitude(m_DivertState.altitude_m);
                        pDivertThisWay->setSpeed(m_DivertState.horizontal_speed_mps);
                        pDivertThisWay->setAltitudeType(m_DivertState.altitude_type);
                        pDivertThisWay->setClimbRate(m_DivertState.vertical_speed_mps);
                        double m_action_time_threshold_s = std::abs(m_DivertState.heading_deg - m_CurrentState.heading_deg)/m_turn_rate_degps; 
                        std::cout << "Maneuver should be held for " << m_action_time_threshold_s << " seconds or until divert heading obtained" << std::endl;
                        m_action_hold_release_time_s = m_CurrentState.time_s + m_action_time_threshold_s;
                        
                        std::shared_ptr<afrl::cmasi::VehicleActionCommand> pAvoidViolation = std::make_shared<afrl::cmasi::VehicleActionCommand>();
                        pAvoidViolation->setCommandID(getUniqueEntitySendMessageId());
                        pAvoidViolation->setVehicleID(m_entityId);
                        pAvoidViolation->setStatus(afrl::cmasi::CommandStatusType::Approved);
                        pAvoidViolation->getVehicleActionList().push_back(pDivertThisWay.release());
                        
                        m_isTakenAction = true;         
                        m_isOnMission = false;
                        //sendLmcpObjectBroadcastMessage(static_cast<avtas::lmcp::Object*>(pAvoidViolation));                
                        sendSharedLmcpObjectBroadcastMessage(pAvoidViolation);
                        std::cout << "ENTITY " << m_entityId << " is conducting a divert maneuver." << std::endl;
                        
                    }
                    else
                    {
                        //TODO: hold conflict until elapsed time for maneuver has passed or until desired state attained--time hold in place
                        //TODO: Compare desired "mode value" to current nogo band and if outside mode value send action command to desired and set isConflict to false
                        if ((m_CurrentState.time_s >= m_action_hold_release_time_s) || isWithinTolerance())  //TODO: add a comparison between current state and desired state to this conditional
                        {
                            m_isTakenAction = false;
                            m_isActionCompleted = true;
                        }
                        std::cout << "Still performing collision avoidance maneuver." << std::endl;

                        //TODO: Evaluate the size of the ConflictResolutionList: if empty do nothing else, if empty and maneuver obtained, flag m_isTakenAction to false
                        //TODO: remove RoW vehicle from the ConflictResolutionList-- done?
                        if (m_isActionCompleted && m_ConflictResolutionList.empty())
                        {
                            //m_isTakenAction = false;
                            //m_isConflict = false;
                            ResetResponse();
                            std::cout << "COMPLETED CURRENT AVOIDANCE MANEUVER." << std::endl;
                            if (isSafeToReturnToMission(pWCVIntervals))
                            {
                                //ResetResponse();
                                if (m_NextWaypoint != -1)
                                {
                                    ResetResponse();
                                    m_isOnMission = true;
                                    std::cout << "Returning to Mission" << std::endl;
                                    m_MissionCommand->setFirstWaypoint(m_NextWaypoint);
                                    sendSharedLmcpObjectBroadcastMessage(m_MissionCommand);
                                }
                            }
                        }
                    }
                }
            }
            else
            {
                if (!m_isOnMission)
                {
                    if (isSafeToReturnToMission(pWCVIntervals))
                    {
                        //ResetResponse();
                        if (m_NextWaypoint != -1)
                        {
                            ResetResponse();
                            m_isOnMission = true;
                            std::cout << "Returning to Mission" << std::endl;
                            m_MissionCommand->setFirstWaypoint(m_NextWaypoint);
                            sendSharedLmcpObjectBroadcastMessage(m_MissionCommand);
                        }
                    }
                    
                }
            }
        }
    }

    return false;
}

} //namespace service
} //namespace uxas

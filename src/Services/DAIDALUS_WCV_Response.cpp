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
#include <string>
#include <vector>
#include <iostream>     // std::cout, cerr, etc

// convenience definitions for the option strings
#define STRING_XML_VEHICLE_ID "VehicleID"
#define STRING_XML_MANEUVERTYPE "ManeuverType"
#define STRING_XML_OPTION_INT "OptionInt"
#define HEADING "Heading"
#define GROUNDSPEED "GroundSpeed"
#define VERTICALSPEED "VerticalSpeed"
#define ALTITUDE "Altitude"

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
    m_VehicleID = m_entityId;

    if (!ndComponent.attribute(STRING_XML_VEHICLE_ID).empty())
    {
        m_VehicleID = ndComponent.attribute(STRING_XML_VEHICLE_ID).as_int();
    }
    

    if (!ndComponent.attribute(STRING_XML_MANEUVERTYPE).empty())
    {
        std::string local_avoidance_maneuver_type = ndComponent.attribute(STRING_XML_MANEUVERTYPE).as_string();
        if (local_avoidance_maneuver_type == HEADING)
        {
            m_AvoidanceManeuverType = local_avoidance_maneuver_type;
        }
        else if (local_avoidance_maneuver_type == GROUNDSPEED)
        {
            m_AvoidanceManeuverType = GROUNDSPEED;
        }
        else if (local_avoidance_maneuver_type == VERTICALSPEED)
        {
            m_AvoidanceManeuverType = VERTICALSPEED;
        }
        else
        {
            m_AvoidanceManeuverType = ALTITUDE;
        }
        
    }
    //TODO: Allow class member variables to be set via xml-- Maneuver type, time thresholds, maneuver offsets from NEAR interval, etc... 
    //TODO: Allow for multiple Response services to be active by using vehicleID passed in via xml in place of m_entityId.--done
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
    m_isCloseToDesired = false;
}
bool DAIDALUS_WCV_Response::isWithinTolerance()
{
    //TODO: extend function to be passed the type of divert maneuver and consider altitude, ground speed, and vertical speed.
    if (m_AvoidanceManeuverType == HEADING)
    {
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
    }
    else if (m_AvoidanceManeuverType == GROUNDSPEED)
    {
        if (std::abs((m_DivertState.horizontal_speed_mps - m_CurrentState.horizontal_speed_mps)) <= m_groundspeed_tolerance_mps)
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
        
    }
    else if (m_AvoidanceManeuverType == VERTICALSPEED)
    {
        if (std::abs((m_DivertState.vertical_speed_mps - m_CurrentState.vertical_speed_mps)) <= m_verticalspeed_tolerance_mps)
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
        
    }
    else
    {
        if (std::abs((m_DivertState.altitude_m - m_CurrentState.altitude_m)) <= m_altitude_tolerance_m)
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
        
    }
    
    if (m_isCloseToDesired && ((m_CurrentState.time_s - m_tolerance_clock_s) >= m_tolerance_threshold_time_s))
    {
        std::cout << "Within Tolerance" << std::endl;
        //std::cout << "DivertState.altitude = " << m_DivertState.altitude_m << " CurrentState.altitude = " << m_CurrentState.altitude_m << std::endl;
        //std::cout << "Current time = " << m_CurrentState.time_s << " Tolerance clock = " << m_tolerance_clock_s << " Tolerance threshold time = " << m_tolerance_threshold_time_s << std::endl;
        return true;
    }
    else
    {
        std::cout << "Not within tolerance" << std::endl;
        return false;
    }
}

void DAIDALUS_WCV_Response::SetDivertState(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals> DAIDALUS_bands)
{
    if (m_AvoidanceManeuverType == HEADING)
    {
        m_DivertState.heading_deg = m_CurrentState.heading_deg;
        std::cout << "Current heading = " << m_CurrentState.heading_deg << std::endl;
        struct intervals
        {
            double lower;
            double upper;
        };
        std::vector<intervals> bands, r_bands;
        intervals temp;
        for (uint i = 0; i < DAIDALUS_bands->getWCVGroundHeadingIntervals().size(); i++)
        {
            temp.lower = DAIDALUS_bands->getWCVGroundHeadingIntervals()[i]->getGroundHeadings()[0];
            temp.upper = DAIDALUS_bands->getWCVGroundHeadingIntervals()[i]->getGroundHeadings()[1];
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
        if (m_DivertState.heading_deg > m_heading_max_deg)  //If divert heading is greater than 360, check to see if a right turn is still possible if not turn left
        {
            for (uint i = 0; i < bands.size(); i++)
            {
                if (isInRange(bands[i].lower, bands[i].upper, std::fmod(m_DivertState.heading_deg + 360.0, 360.0)))
                {
                    m_DivertState.heading_deg = bands[i].upper + m_heading_interval_buffer_deg;
                }
                else
                {
                    break;
                }
                
            }
        }
        
        if (m_DivertState.heading_deg <= (m_CurrentState.heading_deg + 180.0))
        {
            m_DivertState.heading_deg = std::fmod(m_DivertState.heading_deg + 360.0, 360.0);
        }
        else
        {
            for (int i = initial_band; i >= 0; i--)
            {
                if (isInRange(bands[i].lower, bands[i].upper, m_CurrentState.heading_deg))
                {
                    m_DivertState.heading_deg = bands[i].lower - m_heading_interval_buffer_deg;
                }
            }
            if (m_DivertState.heading_deg < m_heading_min_deg)
            {
                for (int i = bands.size(); i >=0; i--)
                {
                    if (isInRange(bands[i].lower, bands[i].upper, std::fmod(m_DivertState.heading_deg + 360.0, 360.0)))
                    {
                        m_DivertState.heading_deg = bands[i].lower - m_heading_interval_buffer_deg;
                    }
                    else
                    {
                        break;
                    }
                    
                }
                
            }
            if (std::fmod(m_DivertState.heading_deg + 360.0, 360.0) >= std::fmod((m_CurrentState.heading_deg -180.0) + 360.0, 360.0))
            {
                m_DivertState.heading_deg = std::fmod(m_DivertState.heading_deg + 360.0, 360.0);
            }
            else if (DAIDALUS_bands->getRecoveryGroundHeadingIntervals().size() >0)
            {
                    //m_DivertState.heading_deg = m_CurrentState.heading_deg;
                bool isRecoveryFound = false;
                for (uint i = 0; i < DAIDALUS_bands->getRecoveryGroundHeadingIntervals().size(); i++)
                {
                    temp.lower = DAIDALUS_bands->getRecoveryGroundHeadingIntervals()[i]->getRecoveryGroundHeadings()[0];
                    temp.upper = DAIDALUS_bands->getRecoveryGroundHeadingIntervals()[i]->getRecoveryGroundHeadings()[1];
                    r_bands.push_back(temp);
                }

                for (uint i = 0; i < r_bands.size(); i++)
                {
                    if ((r_bands[i].lower > m_CurrentState.heading_deg) && (r_bands[i].upper > m_CurrentState.heading_deg))
                    {
                        m_DivertState.heading_deg = r_bands[i].lower + m_heading_interval_buffer_deg / 2.0;
                        isRecoveryFound = true;
                        break;
                    }
                }

                if (!isRecoveryFound)
                {
                    for (int i = r_bands.size(); i >= 0; i--)
                        if ((r_bands[i].lower < m_CurrentState.heading_deg) && (r_bands[i].upper < m_CurrentState.heading_deg))
                        {
                            m_DivertState.heading_deg = r_bands[i].upper - m_heading_interval_buffer_deg / 2.0;
                            break;
                        }
                }
            
                std::cout << "No way to avoid violation of Well Clear Volume" << std::endl;
                std::cout << std::endl;
               //use right turn recovery band
            }
        }
        //TODO: Determine recommended action from DAIDALUS--done
        //TODO: set action response to aforementioned recommended action--done
        //TODO: ensure divert action does not violate keep out zones
        //TODO: send vehicle action command--done
        //TODO: remove RoW vehicle from the ConflictResolutionList--done by nature of the loop
        //m_DivertState.heading_deg = m_CurrentState.heading_deg + 90.0;  //make sure heading is from 0 to 360
        std::cout << "Divert to heading " << m_DivertState.heading_deg << std::endl;
        m_DivertState.altitude_m = m_CurrentState.altitude_m;
        m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;
        m_DivertState.vertical_speed_mps = m_CurrentState.vertical_speed_mps;       
    }
    else if (m_AvoidanceManeuverType == GROUNDSPEED)
    {
        m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;
        struct intervals
        {
            double lower;
            double upper;
        };
        std::vector<intervals> bands, r_bands;
        intervals temp;
        for (uint i = 0; i < DAIDALUS_bands->getWCVGroundSpeedIntervals().size(); i++)
        {
            temp.lower = DAIDALUS_bands->getWCVGroundSpeedIntervals()[i]->getGroundSpeeds()[0];
            temp.upper = DAIDALUS_bands->getWCVGroundSpeedIntervals()[i]->getGroundSpeeds()[1];
            bands.push_back(temp);
        }
        
        uint initial_band = 0;  //band that the initial heading was in.
        bool isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
        for (uint i = 0; i < bands.size(); i++)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.horizontal_speed_mps))
            {
                m_DivertState.horizontal_speed_mps = bands[i].upper + m_groundspeed_interval_buffer_mps;
                if (!isFound)
                {
                    initial_band = i;
                    isFound = true;
                }
            }
        }
        
        if (m_DivertState.horizontal_speed_mps > m_ground_speed_max_mps)  //If divert heading is greater than 360, a left turn is preferred.
        {
            for (int i = initial_band; i >= 0; i--)
            {
                if (isInRange(bands[i].lower, bands[i].upper, m_CurrentState.horizontal_speed_mps))
                {
                    m_DivertState.horizontal_speed_mps = bands[i].lower - m_groundspeed_interval_buffer_mps;
                }
            }
        }
        
        if ((m_DivertState.horizontal_speed_mps < m_ground_speed_min_mps) && (DAIDALUS_bands->getRecoveryGroundSpeedIntervals().size() > 0)) //If after checking right turns and left turns no better heading found, keep current heading
        {
            m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;
            bool isRecoveryFound = false;
            for (uint i = 0; i < DAIDALUS_bands->getRecoveryGroundSpeedIntervals().size(); i++)
            {
                temp.lower = DAIDALUS_bands->getRecoveryGroundSpeedIntervals()[i]->getRecoveryGroundSpeeds()[0];
                temp.upper = DAIDALUS_bands->getRecoveryGroundSpeedIntervals()[i]->getRecoveryGroundSpeeds()[1];
                r_bands.push_back(temp);
            }
            
            for (uint i = 0; i < r_bands.size(); i++)
            {
                if ((r_bands[i].lower > m_CurrentState.horizontal_speed_mps) && (r_bands[i].upper > m_CurrentState.horizontal_speed_mps))
                {
                    m_DivertState.horizontal_speed_mps = r_bands[i].lower + m_groundspeed_interval_buffer_mps / 2.0;
                    isRecoveryFound = true;
                    break;
                }
            }
            
            if (!isRecoveryFound)
            {
                for (int i = r_bands.size(); i >= 0; i--)
                    if ((r_bands[i].lower < m_CurrentState.horizontal_speed_mps) && (r_bands[i].upper < m_CurrentState.horizontal_speed_mps))
                    {
                        m_DivertState.horizontal_speed_mps = r_bands[i].upper - m_groundspeed_interval_buffer_mps / 2.0;
                        break;
                    }
            }
            
        }
        
        m_DivertState.altitude_m = m_CurrentState.altitude_m;
        m_DivertState.heading_deg = m_CurrentState.heading_deg;
        m_DivertState.vertical_speed_mps = m_CurrentState.vertical_speed_mps;        
    }
    else if (m_AvoidanceManeuverType == VERTICALSPEED)
    {
        m_DivertState.vertical_speed_mps = m_CurrentState.vertical_speed_mps;
        struct intervals
        {
            double lower;
            double upper;
        };
        std::vector<intervals> bands, r_bands;
        intervals temp;
        for (uint i = 0; i < DAIDALUS_bands->getWCVVerticalSpeedIntervals().size(); i++)
        {
            temp.lower = DAIDALUS_bands->getWCVVerticalSpeedIntervals()[i]->getVerticalSpeeds()[0];
            temp.upper = DAIDALUS_bands->getWCVVerticalSpeedIntervals()[i]->getVerticalSpeeds()[1];
            bands.push_back(temp);
        }
        
        uint initial_band = 0;  //band that the initial heading was in.
        bool isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
        for (uint i = 0; i < bands.size(); i++)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.vertical_speed_mps))
            {
                m_DivertState.vertical_speed_mps = bands[i].upper + m_verticalspeed_interval_buffer_mps;
                if (!isFound)
                {
                    initial_band = i;
                    isFound = true;
                }
            }
        }
        
        if (m_DivertState.vertical_speed_mps > m_vertical_speed_max_mps)  //If divert heading is greater than 360, a left turn is preferred.
        {
            for (int i = initial_band; i >= 0; i--)
            {
                if (isInRange(bands[i].lower, bands[i].upper, m_CurrentState.vertical_speed_mps))
                {
                    m_DivertState.vertical_speed_mps = bands[i].lower - m_verticalspeed_interval_buffer_mps;
                }
            }
        }
        
        if ((m_DivertState.vertical_speed_mps < m_vertical_speed_min_mps) && (DAIDALUS_bands->getRecoveryVerticalSpeedIntervals().size() > 0))//If after checking right turns and left turns no better heading found, keep current heading
        {
            //m_DivertState.vertical_speed_mps = m_CurrentState.vertical_speed_mps;
            bool isRecoveryFound = false;
            for (uint i = 0; i < DAIDALUS_bands->getRecoveryVerticalSpeedIntervals().size(); i++)
            {
                temp.lower = DAIDALUS_bands->getRecoveryVerticalSpeedIntervals()[i]->getRecoveryVerticalSpeed()[0];
                temp.upper = DAIDALUS_bands->getRecoveryVerticalSpeedIntervals()[i]->getRecoveryVerticalSpeed()[1];
                r_bands.push_back(temp);
            }
            
            for (uint i = 0; i < bands.size(); i++)
            {
                if ((r_bands[i].lower > m_CurrentState.vertical_speed_mps) && (r_bands[i].upper > m_CurrentState.vertical_speed_mps))
                {
                    m_DivertState.vertical_speed_mps = r_bands[i].lower + m_verticalspeed_interval_buffer_mps / 2.0;
                    isRecoveryFound = true;
                    break;
                }
            }
            
            if (!isRecoveryFound)
            {
                for (int i = r_bands.size(); i >= 0; i--)
                    if ((r_bands[i].lower < m_CurrentState.vertical_speed_mps) && (r_bands[i].upper < m_CurrentState.vertical_speed_mps))
                    {
                        m_DivertState.vertical_speed_mps = r_bands[i].upper - m_verticalspeed_interval_buffer_mps / 2.0;
                        break;
                    }
            }
        }
        
        m_DivertState.altitude_m = m_CurrentState.altitude_m;
        m_DivertState.heading_deg = m_CurrentState.heading_deg;
        m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;        
    }
    else
    {
        m_DivertState.altitude_m = m_CurrentState.altitude_m;
        struct intervals
        {
            double lower;
            double upper;
        };
        std::vector<intervals> bands, r_bands;
        intervals temp;
        for (uint i = 0; i < DAIDALUS_bands->getWCVAlitudeIntervals().size(); i++)
        {
            temp.lower = DAIDALUS_bands->getWCVAlitudeIntervals()[i]->getAltitude()[0];
            temp.upper = DAIDALUS_bands->getWCVAlitudeIntervals()[i]->getAltitude()[1];
            bands.push_back(temp);
        }
        
        uint initial_band = 0;  //band that the initial heading was in.
        bool isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
        for (uint i = 0; i < bands.size(); i++)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.altitude_m))
            {
                m_DivertState.altitude_m = bands[i].upper + m_altitude_interval_buffer_m;
                if (!isFound)
                {
                    initial_band = i;
                    isFound = true;
                }
            }
        }
        
        if (m_DivertState.altitude_m > m_altitude_max_m)  //If divert heading is greater than 360, a left turn is preferred.
        {
            for (int i = initial_band; i >= 0; i--)
            {
                if (isInRange(bands[i].lower, bands[i].upper, m_CurrentState.altitude_m))
                {
                    m_DivertState.altitude_m = bands[i].lower - m_altitude_interval_buffer_m;
                }
            }
        }
        
        if ((m_DivertState.altitude_m < m_altitude_min_m) && (DAIDALUS_bands->getRecoveryAltitudeIntervals().size() > 0))//If after checking right turns and left turns no better heading found, keep current heading
        {
            //m_DivertState.altitude_m = m_CurrentState.altitude_m;
            bool isRecoveryFound = false;
            for (uint i = 0; i < DAIDALUS_bands->getRecoveryAltitudeIntervals().size(); i++)
            {
                temp.lower = DAIDALUS_bands->getRecoveryAltitudeIntervals()[i]->getRecoveryAltitude()[0];
                temp.upper = DAIDALUS_bands->getRecoveryAltitudeIntervals()[i]->getRecoveryAltitude()[1];
                r_bands.push_back(temp);
            }
            
            for (uint i = 0; i < r_bands.size(); i++)
            {
                if ((r_bands[i].lower > m_CurrentState.altitude_m) && (r_bands[i].upper > m_CurrentState.altitude_m))
                {
                    m_DivertState.altitude_m = r_bands[i].lower + m_altitude_interval_buffer_m / 2.0;
                    isRecoveryFound = true;
                    break;
                }
            }
            
            if (!isRecoveryFound)
            {
                for (int i = r_bands.size(); i >= 0; i--)
                    if ((r_bands[i].lower < m_CurrentState.altitude_m) && (r_bands[i].upper < m_CurrentState.altitude_m))
                    {
                        m_DivertState.altitude_m = r_bands[i].upper - m_altitude_interval_buffer_m / 2.0;
                        break;
                    }
            }
            std::cout << "No way to avoid violation of Well Clear Volume" << std::endl;
            std::cout << std::endl;
        }
        //m_DivertState.altitude_m = m_CurrentState.altitude_m + 450; //testing change altitude
        m_DivertState.vertical_speed_mps = 0.0; //m_CurrentState.vertical_speed_mps;--"fix" for inconsistency in DivertState.
        m_DivertState.heading_deg = m_CurrentState.heading_deg;
        m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;        
    }
}

bool DAIDALUS_WCV_Response::isSafeToReturnToMission(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals> DAIDALUS_bands)
{
    //TODO:  accept maneuver type as a parameter and consider safe to return for altitude, ground speed, and vertical speed maneuvers.
    //TODO:  maybe add distance to intruders > DMD as a condition on safe to return.
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
        bool isReturnHeadingSafe = true;
        bool isReturnAltitudeSafe = true;
        bool isReturnHorizontalSpeedSafe = true;
        bool isReturnVerticalSpeedSafe = true;
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
        std::cout << "The return to mission horizontal speed is " << m_ReturnState.horizontal_speed_mps << " m/s." << std::endl;
        std::cout << "The return to mission vertical speed is " << m_ReturnState.vertical_speed_mps << " m/s." << std::endl;
        std::cout << "The return to mission altitude is " << m_ReturnState.altitude_m << " m." << std::endl;
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
        
        if (isFound && DAIDALUS_bands->getWCVGroundHeadingRegions()[initial_band] == larcfm::DAIDALUS::BandsRegion::NEAR)
        {
            isReturnHeadingSafe = false;
        }
//        
        bands.clear();
        for (uint i = 0; i < DAIDALUS_bands->getWCVGroundSpeedIntervals().size(); i++)
        {
            temp.lower = DAIDALUS_bands->getWCVGroundSpeedIntervals()[i]->getGroundSpeeds()[0];
            temp.upper = DAIDALUS_bands->getWCVGroundSpeedIntervals()[i]->getGroundSpeeds()[1];
            bands.push_back(temp);
        }
        
        initial_band = UINT32_MAX;  //band that the Return to Mission heading was in.
        isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
        for (uint i = 0; i < bands.size(); i++)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_ReturnState.horizontal_speed_mps))
            {
                initial_band = i;
                isFound = true;
                break;
            }
        }
        
        if (isFound && DAIDALUS_bands->getWCVGroundSpeedRegions()[initial_band] == larcfm::DAIDALUS::BandsRegion::NEAR)
        {
            isReturnHorizontalSpeedSafe = false;
        }
 //
        bands.clear();
        for (uint i = 0; i < DAIDALUS_bands->getWCVVerticalSpeedIntervals().size(); i++)
        {
            temp.lower = DAIDALUS_bands->getWCVVerticalSpeedIntervals()[i]->getVerticalSpeeds()[0];
            temp.upper = DAIDALUS_bands->getWCVVerticalSpeedIntervals()[i]->getVerticalSpeeds()[1];
            bands.push_back(temp);
        }
        
        initial_band = UINT32_MAX;  //band that the Return to Mission heading was in.
        isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
        for (uint i = 0; i < bands.size(); i++)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_ReturnState.vertical_speed_mps))
            {
                initial_band = i;
                isFound = true;
                break;
            }
        }
        
        if (isFound && DAIDALUS_bands->getWCVVerticalSpeedRegions()[initial_band] == larcfm::DAIDALUS::BandsRegion::NEAR)
        {
            isReturnVerticalSpeedSafe = false;
        }
        
//        
        bands.clear();
        for (uint i = 0; i < DAIDALUS_bands->getWCVAlitudeIntervals().size(); i++)
        {
            temp.lower = DAIDALUS_bands->getWCVAlitudeIntervals()[i]->getAltitude()[0];
            temp.upper = DAIDALUS_bands->getWCVAlitudeIntervals()[i]->getAltitude()[1];
            bands.push_back(temp);
        }
        
        initial_band = UINT32_MAX;  //band that the Return to Mission heading was in.
        isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
        for (uint i = 0; i < bands.size(); i++)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_ReturnState.altitude_m))
            {
                initial_band = i;
                isFound = true;
                break;
            }
        }
        
        if (isFound && DAIDALUS_bands->getWCVAltitudeRegions()[initial_band] == larcfm::DAIDALUS::BandsRegion::NEAR)
        {
            isReturnAltitudeSafe = false;
        }

        if (isReturnHeadingSafe && isReturnHorizontalSpeedSafe && isReturnVerticalSpeedSafe && isReturnAltitudeSafe)
        {
            return true;
        }
        else
        {
            std::cout << "NOT SAFE TO RETURN TO MISSION" << std::endl;
            std::cout << std::endl;
            return false;
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
            if (pAutoResponse->getMissionCommandList()[i]->getVehicleID() == m_VehicleID)
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
        if (pMissionCommand->getVehicleID() == m_VehicleID)
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
    else if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<afrl::cmasi::AirVehicleState> pAirVehicleState = 
                std::static_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpMessage->m_object);
        if (pAirVehicleState->getID() == m_VehicleID)
        {
            m_CurrentState.altitude_m = pAirVehicleState->getLocation()->getAltitude();
            m_CurrentState.heading_deg = std::fmod(pAirVehicleState->getCourse()+360.0,360.0); //Course reported between -180 and 180 deg
            m_CurrentState.horizontal_speed_mps = pAirVehicleState->getGroundspeed();
            m_CurrentState.vertical_speed_mps = pAirVehicleState->getVerticalSpeed();
            m_CurrentState.latitude_deg = pAirVehicleState->getLocation()->getLatitude();
            m_CurrentState.longitude_deg = pAirVehicleState->getLocation()->getLongitude();
            m_CurrentState.altitude_type = pAirVehicleState->getLocation()->getAltitudeType();
            m_CurrentState.speed_type = afrl::cmasi::SpeedType::Groundspeed;
            m_CurrentState.total_velocity_mps = pAirVehicleState->getAirspeed();
            m_CurrentState.time_s = pAirVehicleState->getTime()*MILLISECONDSTOSECONDS;
            if (m_isOnMission)
            {
                m_NextWaypoint = pAirVehicleState->getCurrentWaypoint();
                m_isReadyToActWaypoint = true;
                //std::cout << "DAIDALUS Response has the next waypoint" << std::endl;
            }
        }
    }
    else if (larcfm::DAIDALUS::isDAIDALUSConfiguration(receivedLmcpMessage->m_object))
    {
        std::shared_ptr<larcfm::DAIDALUS::DAIDALUSConfiguration> configuration = 
                std::static_pointer_cast<larcfm::DAIDALUS::DAIDALUSConfiguration>(receivedLmcpMessage->m_object);
        m_alertlevels_count = configuration->getRTCAAlertLevels();
        if (m_alertlevels_count == 1)
        {
            m_action_time_threshold_s = configuration->getAlertTime1();
        }
        else if (m_alertlevels_count ==2)
        {
            m_action_time_threshold_s = configuration->getAlertTime2();
        }
        else
        {
            m_action_time_threshold_s = configuration->getAlertTime3();
        }
        
        m_vertical_rate_mps = configuration->getVerticalRate();
        m_horizontal_accel_mpsps = configuration->getHorizontalAcceleration();
        m_vertical_accel_G = configuration->getVerticalAcceleration();
        m_turn_rate_degps = configuration->getTurnRate();
        m_ground_speed_max_mps = configuration->getMaxGroundSpeed();
        m_ground_speed_min_mps = configuration->getMinGroundSpeed();
        m_vertical_speed_max_mps = configuration->getMaxVerticalSpeed();
        m_vertical_speed_min_mps = configuration->getMinVerticalSpeed();
        m_altitude_max_m = configuration->getMaxAltitude();
        m_altitude_min_m = configuration->getMinAltitude();
        m_isReadyToActConfiguration = true;  //boolean indicating if a threshold time is set from reading a DAIDALUS configuration parameter.
        //std::cout << "DAIDALUS Response has received the DAIDALUS configuration used for detection." << std::endl;
    }
    else if (larcfm::DAIDALUS::isWellClearViolationIntervals(receivedLmcpMessage->m_object))
    {
        //std::cout << "DAIDALUS Response has received a violation message." << std::endl;
        //if (m_isReadyToActWaypoint && m_isReadyToActMissionCommand && m_isReadyToActConfiguration)
        std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals> pWCVIntervals = 
                std::static_pointer_cast<larcfm::DAIDALUS::WellClearViolationIntervals> (receivedLmcpMessage->m_object);
        if (m_isReadyToActMissionCommand && m_isReadyToActConfiguration)
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
            
            if (!m_isConflict && m_ConflictResolutionList.size() > 0) //TODO: add check for current heading in NEAR to conditional for action.--done via m_ConflictResolutionList size
            {
                m_isConflict = true;//bool t = SetisConflict(true);
            }
            
            if (m_isConflict)
            {
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
                
                if (m_VehicleID < m_RoW)
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
                        SetDivertState(pWCVIntervals);
                        std::unique_ptr<afrl::cmasi::FlightDirectorAction> pDivertThisWay = uxas::stduxas::make_unique<afrl::cmasi::FlightDirectorAction>();
                        pDivertThisWay->setHeading(static_cast<float>(m_DivertState.heading_deg)); 
                        pDivertThisWay->setAltitude(m_DivertState.altitude_m);
                        pDivertThisWay->setSpeed(m_DivertState.horizontal_speed_mps);
                        pDivertThisWay->setAltitudeType(m_DivertState.altitude_type);
                        pDivertThisWay->setClimbRate(m_DivertState.vertical_speed_mps);
                        double m_action_time_threshold_s = 0;
                        if (((m_turn_rate_degps == 0) && (m_bank_angle_deg == 0)) || (m_horizontal_accel_mpsps == 0) || (m_vertical_accel_G == 0) ||
                                (m_vertical_rate_mps == 0))
                        {
                            m_action_time_threshold_s = 68;
                        }
                        else if (m_AvoidanceManeuverType == HEADING)
                        {
                            if (m_turn_rate_degps != 0)
                            {
                                m_action_time_threshold_s = std::abs(m_DivertState.heading_deg - m_CurrentState.heading_deg) / m_turn_rate_degps; //TODO: handle DAIDALUS configuration using instantaneous bands
                            }
                            else
                            {
                                double estimate_turn_rate_degps = (9.81*std::tan(m_bank_angle_deg * n_Const::c_Convert::dDegreesToRadians())) / 
                                m_CurrentState.total_velocity_mps;
                                m_action_time_threshold_s = std::abs(m_DivertState.heading_deg - m_CurrentState.heading_deg) / estimate_turn_rate_degps;
                            }
                            
                        }
                        else if (m_AvoidanceManeuverType == GROUNDSPEED)
                        {
                            m_action_time_threshold_s = std::abs(m_DivertState.horizontal_speed_mps - m_CurrentState.horizontal_speed_mps) / 
                                    m_horizontal_accel_mpsps;
                        }
                        else if (m_AvoidanceManeuverType == VERTICALSPEED)
                        {
                            m_action_time_threshold_s = std::abs(m_DivertState.vertical_speed_mps - m_CurrentState.vertical_speed_mps) / 
                                    (m_vertical_accel_G * 9.81);
                        }
                        else
                        {
                            m_action_time_threshold_s = std::abs(m_DivertState.altitude_m - m_CurrentState.altitude_m) / 
                                    (m_vertical_speed_max_mps) + std::abs(m_vertical_speed_max_mps - m_CurrentState.vertical_speed_mps) / 
                                    (m_vertical_accel_G * 9.81);
                        }
                        
                        std::cout << "Maneuver should be held for " << m_action_time_threshold_s << " seconds or until divert heading obtained" << std::endl;
                        m_action_hold_release_time_s = m_CurrentState.time_s + m_action_time_threshold_s;
                        
                        std::shared_ptr<afrl::cmasi::VehicleActionCommand> pAvoidViolation = std::make_shared<afrl::cmasi::VehicleActionCommand>();
                        pAvoidViolation->setCommandID(getUniqueEntitySendMessageId());
                        pAvoidViolation->setVehicleID(m_VehicleID);
                        pAvoidViolation->setStatus(afrl::cmasi::CommandStatusType::Approved);
                        pAvoidViolation->getVehicleActionList().push_back(pDivertThisWay.release());
                        
                        m_isTakenAction = true;         
                        m_isOnMission = false;
                        //sendLmcpObjectBroadcastMessage(static_cast<avtas::lmcp::Object*>(pAvoidViolation));                
                        sendSharedLmcpObjectBroadcastMessage(pAvoidViolation);
                        std::cout << "ENTITY " << m_VehicleID << " is conducting a divert maneuver." << std::endl;                        
                    }
                    else
                    {
                        //TODO: hold conflict until elapsed time for maneuver has passed or until desired state attained--time hold in place--done
                        //TODO: Compare desired "mode value" to current nogo band and if outside mode value send action command to desired and set isConflict to false--done
                        //if ((m_CurrentState.time_s >= m_action_hold_release_time_s) || isWithinTolerance())  //TODO: add a comparison between current state and desired state to this conditional--done
                        if (isWithinTolerance())
                        {
                            m_isTakenAction = false;
                            m_isActionCompleted = true;
                            m_isCloseToDesired = false;
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
                                    //ResetResponse();
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
                            //ResetResponse();
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

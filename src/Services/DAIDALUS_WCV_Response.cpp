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
bool DAIDALUS_WCV_Response::foundWCVHeadingResolution(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands)
{
    bool guaranteed_flag = true;
    m_DivertState.heading_deg = m_CurrentState.heading_deg;
    m_DivertState.altitude_m = m_CurrentState.altitude_m;
    m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;
    m_DivertState.vertical_speed_mps = 0; // hold current altitude while diverting m_CurrentState.vertical_speed_mps;       

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
//        std::cout << "Lower = " << temp.lower << std::endl;
//        std::cout << "Upper = " << temp.upper << std::endl;
    }
//    std::cout << std::endl;
    if (bands.size() == 0)
    {
        //Expected conflict bands but found none--set divert state to current state
        return false;
    }
    uint initial_band = 0;  //band that the initial heading was in.
    bool isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
    //Of the reported bad bands, find which one the current heading is in
    for (uint i = 0; i < bands.size(); i++) //loop over the bands trying to set divert action to the maximum (right hand turn) of an interval until no 
        //more consecutive intervals are found
    {
        if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.heading_deg))
        {
            m_DivertState.heading_deg = bands[i].upper + m_heading_interval_buffer_deg; //set divert heading to just over the maximum of the interval that current heading was found in
            if (!isFound)
            {
                initial_band = i;
                isFound = true;
            }
        }
    }
    if (m_DivertState.heading_deg > m_heading_max_deg)  //If divert heading is greater than 360, check to see if a right turn is still possible if not turn left
    {
        // this loop checks the angle wrapped form of the divert action to see if increased turn to the right can find a heading that is not in conflict
        // process terminates immediately when a conflict interval does not contain the candidate divert heading
        for (uint i = 0; i < bands.size(); i++)
        {
            if (isInRange(bands[i].lower, bands[i].upper, std::fmod(m_DivertState.heading_deg + 360.0, 360.0)))
            {
                m_DivertState.heading_deg = bands[i].upper + m_heading_interval_buffer_deg; // if angle wrapped divert heading is found in an interval,
                //set divert heading to just over the maximum of the interval
            }
            else
            {
                break;
            }

        }
    }

    if (std::fmod(m_DivertState.heading_deg +360.0, 360.0) <= std::fmod((m_CurrentState.heading_deg + 180.0)+360.0, 360.0))
    {
        m_DivertState.heading_deg = std::fmod(m_DivertState.heading_deg + 360.0, 360.0);
    }
    else 
    {
        //this branch attempts to find a left turn for divert heading by looping over the intervals from last to first--already know some bands exist
        m_DivertState.heading_deg = m_CurrentState.heading_deg;
        for (int i = initial_band; i >= 0; i--)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.heading_deg))
            {
                m_DivertState.heading_deg = bands[i].lower - m_heading_interval_buffer_deg; // set divert heading to just under the interval minimum 
                // that contains the current heading--loop over the bands from the current band to the initial band
            }
        }
        if (m_DivertState.heading_deg < m_heading_min_deg)  //check for angle wrap if candidate divert heading is less than the minimum
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
            guaranteed_flag = false;
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
        else
        {
            guaranteed_flag = false;
            std::cout << "No resolution found. Divert heading is " << m_DivertState.heading_deg << std::endl;
            std::cout << std::endl;
        }
    }
    //TODO: Determine recommended action from DAIDALUS--done
    //TODO: set action response to aforementioned recommended action--done
    //TODO: ensure divert action does not violate keep out zones
    //TODO: send vehicle action command--done
    //TODO: remove RoW vehicle from the ConflictResolutionList--done by nature of the loop
    //m_DivertState.heading_deg = m_CurrentState.heading_deg + 90.0;  //make sure heading is from 0 to 360
    std::cout << "Divert to heading " << m_DivertState.heading_deg << std::endl;
    return guaranteed_flag;

}
bool DAIDALUS_WCV_Response::foundWCVGroundSpeedResolution(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands)
{
    //slower speeds preferred
    bool guaranteed_flag = true;
    m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;
    m_DivertState.altitude_m = m_CurrentState.altitude_m;
    m_DivertState.heading_deg = m_CurrentState.heading_deg;
    m_DivertState.vertical_speed_mps = 0;   //hold altitude while divertingm_CurrentState.vertical_speed_mps;
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
    if (bands.size()== 0)
    {
        //unexpected result
        std::cout << "Expected conflict bands but found none." << std::endl;
        return false;
    }
    uint initial_band = 0;  //band that the initial heading was in.
    for (uint i = 0; i < bands.size(); i++)
    {
        if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.horizontal_speed_mps))
        {
            initial_band = i;
            break;
        }
    }
    
    for (int i = initial_band; i >= 0; i--)
    {
        if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.horizontal_speed_mps))
        {
            m_DivertState.horizontal_speed_mps = bands[i].lower - m_groundspeed_interval_buffer_mps; //if DivertState is in a bad band, alter to less than minimum
        }
    }

    if (m_DivertState.horizontal_speed_mps < m_ground_speed_min_mps)  //If divert speed is less than min, a speed up is preferred.
    {
        m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps; //reset divert horizontal speed to current then check higher speeds
        for (uint i = initial_band; i < bands.size(); i++)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.horizontal_speed_mps))
            {
                m_DivertState.horizontal_speed_mps = bands[i].upper + m_groundspeed_interval_buffer_mps; //if divertstate is in a bad band, alter to more than maximum
            }
        }
    }

    if (m_DivertState.horizontal_speed_mps > m_ground_speed_max_mps)  //If after checking slow downs and speed up no better heading found, check recovery intervals
    {
        guaranteed_flag = false;
        if (DAIDALUS_bands->getRecoveryGroundSpeedIntervals().size() > 0)
        {
            bool isRecoveryFound = false;
            //ASSERT(Recovery bands will never span the entire range)--Need to set recovery volume to start at well clear volume
            //m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;
            //Form vector of recovery intervals
            for (uint i = 0; i < DAIDALUS_bands->getRecoveryGroundSpeedIntervals().size(); i++)
            {
                temp.lower = DAIDALUS_bands->getRecoveryGroundSpeedIntervals()[i]->getRecoveryGroundSpeeds()[0];
                temp.upper = DAIDALUS_bands->getRecoveryGroundSpeedIntervals()[i]->getRecoveryGroundSpeeds()[1];
                r_bands.push_back(temp);
            }

            for (int i = r_bands.size(); i >= 0; i--)
            {
                //Find the first recovery interval that is at a lower speed than current speed
                if ((r_bands[i].lower < m_CurrentState.horizontal_speed_mps) && (r_bands[i].upper < m_CurrentState.horizontal_speed_mps))
                {
                    m_DivertState.horizontal_speed_mps = r_bands[i].upper - m_groundspeed_interval_buffer_mps / 2.0;
                    isRecoveryFound = true;
                    break;
                }
            }

            if (!isRecoveryFound)
            {
                for (uint i = 0; i < r_bands.size(); i++)
                    //If no lower recovery found, find first recovery interval with higher speeds than current
                    if ((r_bands[i].lower > m_CurrentState.horizontal_speed_mps) && (r_bands[i].upper > m_CurrentState.horizontal_speed_mps))
                    {
                        m_DivertState.horizontal_speed_mps = r_bands[i].lower + m_groundspeed_interval_buffer_mps / 2.0;
                        break;
                    }
            }

        }
        else 
        {
            //If no recovery found, set default behavior to minimum speed
            m_DivertState.horizontal_speed_mps = m_ground_speed_min_mps;
        }
    }
    return guaranteed_flag;    
}
bool DAIDALUS_WCV_Response::foundWCVVerticalSpeedResolution(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands)
{
    bool guaranteed_flag = true;
    m_DivertState.vertical_speed_mps = m_CurrentState.vertical_speed_mps;
    m_DivertState.altitude_m = m_CurrentState.altitude_m;
    m_DivertState.heading_deg = m_CurrentState.heading_deg;
    m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;
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
    if (bands.size() == 0)
    {
        //Expected conflict bands but found none--set divert state to current state
        return false;
    }
    uint initial_band = 0;  //band that the initial heading was in.
    bool isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
    //Of the reported bad bands, find which one the current vertical speed is in
    for (uint i = 0; i < bands.size(); i++)
    {
        if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.vertical_speed_mps))
        {
            m_DivertState.vertical_speed_mps = bands[i].upper + m_verticalspeed_interval_buffer_mps; //if DivertState is in a bad band, alter to more than maximum
            if (!isFound)
            {
                initial_band = i;
                isFound = true;
            }
        }
    }

    if (m_DivertState.vertical_speed_mps > m_vertical_speed_max_mps)  //If divert vertical speed  is greater than max, a decrease turn is preferred.
    {
        m_DivertState.vertical_speed_mps = m_CurrentState.vertical_speed_mps; //reset divert speed to current speed and check lowers speeds
        for (int i = initial_band; i >= 0; i--)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_CurrentState.vertical_speed_mps))
            {
                m_DivertState.vertical_speed_mps = bands[i].lower - m_verticalspeed_interval_buffer_mps; //if divert speed in a bad band, alter to less than the minimum
            }
        }
    }

    if (m_DivertState.vertical_speed_mps < m_vertical_speed_min_mps)//If after checking speed increases and decreases no better heading found, check recovery
    {
        guaranteed_flag = false;
        if (DAIDALUS_bands->getRecoveryVerticalSpeedIntervals().size() > 0)
        {
            //m_DivertState.vertical_speed_mps = m_CurrentState.vertical_speed_mps;
            bool isRecoveryFound = false;
            //Form a vector of recovery bands
            for (uint i = 0; i < DAIDALUS_bands->getRecoveryVerticalSpeedIntervals().size(); i++)
            {
                temp.lower = DAIDALUS_bands->getRecoveryVerticalSpeedIntervals()[i]->getRecoveryVerticalSpeed()[0];
                temp.upper = DAIDALUS_bands->getRecoveryVerticalSpeedIntervals()[i]->getRecoveryVerticalSpeed()[1];
                r_bands.push_back(temp);
            }

            for (uint i = 0; i < bands.size(); i++)
            {
                //Find first recovery interval with speeds greater than current and set divert to just over minimum
                if ((r_bands[i].lower > m_CurrentState.vertical_speed_mps) && (r_bands[i].upper > m_CurrentState.vertical_speed_mps))
                {
                    m_DivertState.vertical_speed_mps = r_bands[i].lower + m_verticalspeed_interval_buffer_mps / 2.0;
                    isRecoveryFound = true;
                    break;
                }
            }

            if (!isRecoveryFound)
            {
                //if no faster recovery found, check lower recovery
                for (int i = r_bands.size(); i >= 0; i--)
                    if ((r_bands[i].lower < m_CurrentState.vertical_speed_mps) && (r_bands[i].upper < m_CurrentState.vertical_speed_mps))
                    {
                        m_DivertState.vertical_speed_mps = r_bands[i].upper - m_verticalspeed_interval_buffer_mps / 2.0;
                        break;
                    }
            }
        }

    }
    return guaranteed_flag;
}
bool DAIDALUS_WCV_Response::foundWCVAltitudeResolution(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands)
{
    bool guaranteed_flag = true;
    m_DivertState.altitude_m = m_CurrentState.altitude_m;
    m_DivertState.vertical_speed_mps = 0.0; //m_CurrentState.vertical_speed_mps;--"fix" for inconsistency in DivertState.
    m_DivertState.heading_deg = m_CurrentState.heading_deg;
    m_DivertState.horizontal_speed_mps = m_CurrentState.horizontal_speed_mps;    
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
    if (bands.size() == 0)
    {
        //Expected conflict bands but found none--set divert state to current state (minus vertical speed)
        return false;
    }
    uint initial_band = 0;  //band that the initial heading was in.
    bool isFound = false;  //boolean stating whether the band that the initial heading was in has been identified
    //Of the reported bad bands, find which one the current altitude is in
    for (uint i = 0; i < bands.size(); i++)
    {
        if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.altitude_m))
        {
            m_DivertState.altitude_m = bands[i].upper + m_altitude_interval_buffer_m; //if DivertState is in a bad band, alter to more than maximum
            if (!isFound)
            {
                initial_band = i;
                isFound = true;
            }
        }
    }

    if (m_DivertState.altitude_m > m_altitude_max_m)  //If divert altitude is greater than altitude max, a descent is preferred.
    {
        m_DivertState.altitude_m = m_CurrentState.altitude_m; //reset divert altitude to current altitude then check bands below current altitude
        for (int i = initial_band; i >= 0; i--)
        {
            if (isInRange(bands[i].lower, bands[i].upper, m_DivertState.altitude_m))
            {
                m_DivertState.altitude_m = bands[i].lower - m_altitude_interval_buffer_m; //if Divert altitude is in a bad band, alter to less than minimum
            }
        }
    }

    if (m_DivertState.altitude_m < m_altitude_min_m)//If after checking ascents and descents no better heading found, check recovery bands
    {
        guaranteed_flag = false;
        if (DAIDALUS_bands->getRecoveryAltitudeIntervals().size() > 0)
        {
            //m_DivertState.altitude_m = m_CurrentState.altitude_m;
            bool isRecoveryFound = false;
            //Form a vector of recovery band intervals
            for (uint i = 0; i < DAIDALUS_bands->getRecoveryAltitudeIntervals().size(); i++)
            {
                temp.lower = DAIDALUS_bands->getRecoveryAltitudeIntervals()[i]->getRecoveryAltitude()[0];
                temp.upper = DAIDALUS_bands->getRecoveryAltitudeIntervals()[i]->getRecoveryAltitude()[1];
                r_bands.push_back(temp);
            }

            //Find the first recovery band that is at an altitude greater than the current altitude and set divert altitude to just over the minimum
            for (uint i = 0; i < r_bands.size(); i++)
            {
                if ((r_bands[i].lower > m_CurrentState.altitude_m) && (r_bands[i].upper > m_CurrentState.altitude_m))
                {
                    m_DivertState.altitude_m = r_bands[i].lower + m_altitude_interval_buffer_m / 2.0; 
                    isRecoveryFound = true;
                    break;
                }
            }

            //If no recovery greater than current altitude exists, find the first recovery interval lower than current altitude and set divert to just 
            //under the maximum of that recovery interval
            if (!isRecoveryFound)
            {
                for (int i = r_bands.size(); i >= 0; i--)
                    if ((r_bands[i].lower < m_CurrentState.altitude_m) && (r_bands[i].upper < m_CurrentState.altitude_m))
                    {
                        m_DivertState.altitude_m = r_bands[i].upper - m_altitude_interval_buffer_m / 2.0;
                        break;
                    }
            }
        }
        else
        {
            //if no solution and no recovery found default to diverting to maximum altitude
            guaranteed_flag = false;
            m_DivertState.altitude_m = m_altitude_max_m;
            std::cout << "No way to avoid violation of Well Clear Volume" << std::endl;
            std::cout << std::endl;

        }
        //m_DivertState.altitude_m = m_CurrentState.altitude_m + 450; //testing change altitude
    }
    return guaranteed_flag;
}

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

void DAIDALUS_WCV_Response::SetDivertState(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands)
{
//    if (m_AvoidanceManeuverType == HEADING)
//    {
//        foundWCVHeadingResolution(DAIDALUS_bands);
//    }
//    else if (m_AvoidanceManeuverType == GROUNDSPEED)
//    {
//        foundWCVGroundSpeedResolution(DAIDALUS_bands);
//    }
//    else if (m_AvoidanceManeuverType == VERTICALSPEED)
//    {
//        foundWCVVerticalSpeedResolution(DAIDALUS_bands);
//    }
//    else
//    {
//        foundWCVAltitudeResolution(DAIDALUS_bands);//do stuff
//    }
    bool altitude_resolution_good, heading_resolution_good, groundspeed_resolution_good;
    switch (m_priority)
    {
//        std::cout << std::endl;
//        std::cout << "PRIORITY = " << m_priority << std::endl;
//        std::cout << std::endl;
        case Standard:
            altitude_resolution_good = foundWCVAltitudeResolution(DAIDALUS_bands);
//            std::cout << std::endl;
//            std::cout << "Altitude resolution is good as a " << altitude_resolution_good << " statement." << std::endl;
//            std::cout << std::endl;
            if (!altitude_resolution_good)
            {
                heading_resolution_good = foundWCVHeadingResolution(DAIDALUS_bands);
                if (!heading_resolution_good)
                {
                    groundspeed_resolution_good = foundWCVGroundSpeedResolution(DAIDALUS_bands);
                }
                
            }
            break;
        case High:
            groundspeed_resolution_good = foundWCVGroundSpeedResolution(DAIDALUS_bands);
            if (!groundspeed_resolution_good)
            {
                heading_resolution_good = foundWCVHeadingResolution(DAIDALUS_bands);
                if (!heading_resolution_good)
                {
                    altitude_resolution_good = foundWCVAltitudeResolution(DAIDALUS_bands);
                }
                
            }
            break;
            
    }
    
}

bool DAIDALUS_WCV_Response::isSafeToReturnToMission(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands)
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
        m_priority_time_threshold_s = m_action_time_threshold_s / 2.0;
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
        m_heading_delta_deg = configuration->getTrackStep();
        m_ground_speed_delta_mps = configuration->getGroundSpeedStep();
        m_vertical_speed_delta_mps = configuration->getVerticalSpeedStep();
        m_altitude_delta_m = configuration->getAltitudeStep();
        m_heading_interval_buffer_deg = m_heading_delta_deg / 2.0;
        m_groundspeed_interval_buffer_mps = m_ground_speed_delta_mps / 2.0;
        m_verticalspeed_interval_buffer_mps = m_vertical_speed_delta_mps / 2.0;
        m_altitude_interval_buffer_m = m_altitude_delta_m / 2.0;
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
            std::vector<int64_t> ConflictResolutionList;
            int local_priority = 0;
            for (size_t i = 0; i < pWCVIntervals->getEntityList().size(); i++)
            {
                if (pWCVIntervals->getTimeToViolationList()[i] <= m_action_time_threshold_s)
                {
                    std::cout << "Adding " << pWCVIntervals->getEntityList()[i] << " to the Conflict Resolution List" << std::endl;
                    ConflictResolutionList.push_back(pWCVIntervals->getEntityList()[i]);
                }
                if (pWCVIntervals->getTimeToViolationList()[i] <= m_priority_time_threshold_s)
                {
                    local_priority = local_priority + 1;
                }
            }
            if (local_priority > 0) 
            {
                m_priority = High;
            }
            else
            {
                m_priority = Standard;
            }
            int64_t RoW;
            if (ConflictResolutionList.size() > 0)
            {
                std:: cout << "I HAVE DETERMINED THAT A CONFLICT MUST BE RESOLVED" << std::endl;
                RoW = INT64_MAX;
            }
            else
            {
                RoW = INT64_MIN;
            }
            for (auto i : ConflictResolutionList)
            {
                if (i < RoW)
                {
                    RoW = i;
                }
                std::cout << "A Candidate for the Right of Way vehicle is Entity" << RoW << std::endl;
            }
            if (ConflictResolutionList.size() > 0)
            {
                m_state = InConflict;
            }
            switch (m_state)
            {
                case OnMission:
//                    if (ConflictResolutionList.size() > 0)
//                    {
//                        m_state = InConflict;
//                    }
                    break;
                case InConflict:
                    if (m_VehicleID < RoW)
                    {
                        //Ownship has the Right of Way and therefore should take no action
                        m_state = OnHold;
                    }
                    else
                    {
                        SetDivertState(pWCVIntervals);
                        std::unique_ptr<afrl::cmasi::FlightDirectorAction> pDivertThisWay = uxas::stduxas::make_unique<afrl::cmasi::FlightDirectorAction>();
                        pDivertThisWay->setHeading(static_cast<float>(m_DivertState.heading_deg)); 
                        pDivertThisWay->setAltitude(m_DivertState.altitude_m);
                        pDivertThisWay->setSpeed(m_DivertState.horizontal_speed_mps);
                        pDivertThisWay->setAltitudeType(m_DivertState.altitude_type);
                        pDivertThisWay->setClimbRate(m_DivertState.vertical_speed_mps);
                        std::shared_ptr<afrl::cmasi::VehicleActionCommand> pAvoidViolation = std::make_shared<afrl::cmasi::VehicleActionCommand>();
                        pAvoidViolation->setCommandID(getUniqueEntitySendMessageId());
                        pAvoidViolation->setVehicleID(m_VehicleID);
                        pAvoidViolation->setStatus(afrl::cmasi::CommandStatusType::Approved);
                        pAvoidViolation->getVehicleActionList().push_back(pDivertThisWay.release());
//                        m_isTakenAction = true;         
                        m_isOnMission = false;
                        //sendLmcpObjectBroadcastMessage(static_cast<avtas::lmcp::Object*>(pAvoidViolation));                
                        sendSharedLmcpObjectBroadcastMessage(pAvoidViolation);
                        std::cout << "ENTITY " << m_VehicleID << " is conducting a divert maneuver." << std::endl;  
                        m_state = OnHold;
                        
                    }
                    
                    break;
                case OnHold:
//                    std::cout << "In Hold last command and there are no conflicts detected." << std::endl;
                    if (m_isOnMission)
                    {
                        m_state = OnMission;
                    }
                    else
                    {
                        if (isSafeToReturnToMission(pWCVIntervals))
                        {
                            //send safe to return to mission command
                            if (m_NextWaypoint != -1)
                            {
                                m_MissionCommand->setFirstWaypoint(m_NextWaypoint);
                                sendSharedLmcpObjectBroadcastMessage(m_MissionCommand);
                                m_state = OnMission;
                                m_isOnMission = true;
                            }
                        }
                    }
                    break;
            }
        }
    }

    return false;
}

} //namespace service
} //namespace uxas

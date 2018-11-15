// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   DAIDALUS_WCV_Response.h
 * Author: SeanR
 *
 * Created on June 27 2018
 */

#ifndef UXAS_DAIDALUS_WCV_RESPONSE_H
#define UXAS_DAIDALUS_WCV_RESPONSE_H



#include "Constants/Convert.h"
#include "ServiceBase.h"
#include "afrl/cmasi/Waypoint.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/AltitudeType.h"
#include "afrl/cmasi/SpeedType.h"
#include "larcfm/DAIDALUS/WellClearViolationIntervals.h"

#include <memory>
#include <string>
#include <vector>
namespace uxas
{
namespace service
{

/*! \class DAIDALUS_WCV_Response
    \brief This is a service responds to DAIDALUS Well-Clear Violations by setting the ownship's response to an "imminent" violation
 * 
 * 
 * Configuration String: N/A
 * 
 * Options:
 *   * 
 * Design: TBD
 * 
 * Details: TBD
 * Subscribed Messages:
 *  - afrl::cmasi::AirVehicleState
 *  - larcfm::DAIDALUS::DAIDALUSConfiguration
 *  - larcfm::DAIDALUS::WellClearViolationIntervals
 * 
 * Sent Messages:
 *  - afrl::cmasi::VehicleActionCommand
 * 
 * 
 */

class DAIDALUS_WCV_Response : public ServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="DAIDALUS_WCV_Response". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("DAIDALUS_WCV_Response");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };

    /** \brief If this string is not empty, it is used to create a data 
     * directory to be used by the service. The path to this directory is
     * accessed through the ServiceBase variable m_workDirectoryPath. */
    static const std::string&
    s_directoryName() { static std::string s_string(""); return (s_string); };

    static ServiceBase*
    create()
    {
        return new DAIDALUS_WCV_Response;
    };

    DAIDALUS_WCV_Response();

    virtual
    ~DAIDALUS_WCV_Response();

private:

    static
    ServiceBase::CreationRegistrar<DAIDALUS_WCV_Response> s_registrar;

    /** brief Copy construction not permitted */
    DAIDALUS_WCV_Response(DAIDALUS_WCV_Response const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(DAIDALUS_WCV_Response const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    bool
    start() override;

    bool
    terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

public:
    
    

private:
    enum states {OnMission=1, InConflict, OnHold} m_state{OnMission};
    enum priority {Standard = 1, High = 2} m_priority{Standard};
    int64_t m_VehicleID;
    bool m_isConflict {false};  //boolean stating whether or not a potential WCV has been detected that requires action
    bool m_isOnMission {false};  //boolean stating whether or not UAV is executing waypoints on Mission or not (diverting)
    bool m_isReadyToAct {false};    //boolean stating whether or not service has all necessary prerequisites in order to react to an imminent collision.
    bool m_isTakenAction {false};   //boolean stating whether or not the service has issued a vehicle action command to the ownship.
    bool m_isReadyToActWaypoint {false};    //boolean stating whether or not the service has received a waypoint designating the goal location
    bool m_isReadyToActMissionCommand {false};  //boolean stating whether or not the service has received a mission command that lists all waypoints.
    bool m_isReadyToActConfiguration {false};  //boolean stating whether or not service has received configuration parameters in order to process violation messages
    bool m_isActionCompleted {false}; //boolean stating whether or not service has completed taking action for the violation under consideration.
    bool m_isCloseToDesired {false};
    double m_heading_tolerance_deg{0.5};
    double m_groundspeed_tolerance_mps{5};
    double m_verticalspeed_tolerance_mps{5};
    double m_altitude_tolerance_m{10};
    double m_tolerance_clock_s;
    double m_tolerance_threshold_time_s{5};  //time needed to stay within desired state to be considered attained--seconds
    double m_action_time_threshold_s;   // time threshold to hold when taking action
    double m_priority_time_threshold_s; //time threshold to raise priority level when taking action
    double m_action_hold_release_time_s;  //time at which an action hold must be released
    double m_vertical_rate_mps; //DAIDALUS configuration vertical rate used for estimation of time to perform altitude maneuver
    double m_turn_rate_degps;   //DAIDALUS configuration turn rate used for estimation of time to perform heading/track maneuver
    double m_bank_angle_deg;    //DAIDALUS configuration bank angle used for estimation to time to perform heading/track maneuver
    double m_horizontal_accel_mpsps;    //DAIDALUS configuration horizontal acceleration used for estimation of time to perform a horizontal speed maneuver
    double m_vertical_accel_G;  //DAIDALUS configuration vertical 
    double m_ground_speed_max_mps;  //DAIDALUS configuration maximum horizontal speed
    double m_ground_speed_min_mps; //DAIDALUS configuration minimum horizontal speed
    double m_heading_max_deg{360.0};  //DAIDALUS maximum heading 
    double m_heading_min_deg{0.0};   //DAIDALUS minimum heading 
    double m_vertical_speed_max_mps;    //DAIDALUS configuration maximum vertical speed
    double m_vertical_speed_min_mps;    //DAIDALUS configuration minimum vertical speed
    double m_altitude_max_m;    //DAIDALUS configuration maximum altitude
    double m_altitude_min_m;    //DAIDALS configuration minimum altitude
    double m_heading_delta_deg; //DAIDALUS configuration heading discretization 
    double m_ground_speed_delta_mps;    //DAIDALUS configuration ground speed discretization
    double m_vertical_speed_delta_mps;  //DAIDALUS configuration vertical speed discretization
    double m_altitude_delta_m;  //DAIDALUS configuration altitude discretization
    double m_heading_interval_buffer_deg{5.0};  //degrees to buffer the heading bands interval by for avoidance maneuver
    double m_groundspeed_interval_buffer_mps{10.0};   //speed to buffer the ground speed interval by for avoidance maneuver.
    double m_verticalspeed_interval_buffer_mps{5.0};  //speed to buffer the vertical speed interval by for avoidance maneuver.
    double m_altitude_interval_buffer_m{20.0};    //distance in meters to buffer the altitude interval by for avoidance maneuver.
    int64_t m_NextWaypoint{-1};// {nullptr};
    int64_t m_RoW;
    uint16_t m_alertlevels_count;
    std::shared_ptr<afrl::cmasi::MissionCommand> m_MissionCommand{nullptr};// {nullptr};
    std::string m_AvoidanceManeuverType = "Heading";
    std::vector<int64_t> m_ConflictResolutionList;

    struct State
    {
        double altitude_m;
        double horizontal_speed_mps;
        double vertical_speed_mps;
        double heading_deg;
        double latitude_deg;
        double longitude_deg;
        double time_s;
        double total_velocity_mps;
        afrl::cmasi::AltitudeType::AltitudeType altitude_type;
        afrl::cmasi::SpeedType::SpeedType speed_type;
    }m_CurrentState, m_DivertState, m_ReturnState;
    void ResetResponse();
    void SetDivertState(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands);
    bool isWithinTolerance();
    bool isSafeToReturnToMission(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_band);
    bool foundWCVAltitudeResolution(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands);
    bool foundWCVVerticalSpeedResolution(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands);
    bool foundWCVGroundSpeedResolution(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands);
    bool foundWCVHeadingResolution(const std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>& DAIDALUS_bands);
    
   };

} //namespace service
} //namespace uxas

#endif /* UXAS_DAIDALUS_WCV_RESPONSE_H */


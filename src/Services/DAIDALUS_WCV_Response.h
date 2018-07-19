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

#include <memory>
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
    bool m_isConflict {false};  //boolean stating whether or not a potential WCV has been detected that requires action
    bool m_isReadyToAct {false};    //boolean stating whether or not service has all necessary prerequisites in order to react to an imminent collision.
    bool m_isTakenAction {false};   //boolean stating whether or not the service has issued a vehicle action command to the ownship.
    bool m_isReadyToActWaypoint {false};    //boolean stating whether or not the service has received a waypoint designating the goal location
    bool m_isReadyToActMissionCommand {false};  //boolean stating whether or not the service has received a mission command that lists all waypoints.
    bool m_isReadyToActConfiguration {false};  //boolean stating whether or not service has received configuration parameters in order to process violation messages
    double m_action_time_threshold_s;   // time threshold to determine taking action
    double m_vertical_rate_mps; //DAIDALUS configuration vertical rate used for estimation of time to perform altitude maneuver
    double m_turn_rate_degps;   //DAIDALUS configuration turn rate used for estimation of time to perform heading/track maneuver
    double m_horizontal_accel_mpsps;    //DAIDALUS configuration horizontal acceleration used for estimation of time to perform a horizontal speed maneuver
    double m_vertical_accel_mpsps;  //DAIDALUS configuration vertical 
    int64_t  m_NextWaypoint;// {nullptr};
    std::shared_ptr<afrl::cmasi::MissionCommand> m_MissionCommand;// {nullptr};
    std::vector<int64_t> m_ConflictResolutionList;
    bool SetisConflict(bool& val);
    bool GetisConflict();
    struct DesiredState
    {
        double altitude_m;
        double horizontal_speed_mps;
        double vertical_speed_mps;
        double heading_deg;
    }m_DesiredState;
    struct CurrentState
    {
        double altitude_m;
        double horizontal_speed_mps;
        double vertical_speed_mps;
        double heading_deg;
        double latitude_deg;
        double longitude_deg;
        afrl::cmasi::AltitudeType::AltitudeType altitude_type;
        afrl::cmasi::SpeedType::SpeedType speed_type;
    }m_CurrentState;

    
    
   };

} //namespace service
} //namespace uxas

#endif /* UXAS_DAIDALUS_WCV_RESPONSE_H */


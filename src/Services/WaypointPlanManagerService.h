// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_WaypointPlanManager.h
 * Author: steve
 *
 * Created on December 16, 2014, 4:47 PM
 */

#ifndef UXAS_SERVICE_WAYPOINT_PLAN_MANAGER_SERVICE_H
#define UXAS_SERVICE_WAYPOINT_PLAN_MANAGER_SERVICE_H


//#include "WaypointManager.h"
#include "ServiceBase.h"
#include "TypeDefs/UxAS_TypeDefs_String.h"
#include "CallbackTimer.h"


#include "afrl/cmasi/Waypoint.h"
#include "afrl/cmasi/TurnType.h"
#include "afrl/cmasi/MissionCommand.h"

#include <cstdint> // uint32_t

namespace uxas
{
namespace service
{


/*! \class WaypointPlanManagerService
    \brief A service that serves plans to a vehicle interface.

 * 1) Receive AutomationResponse/MissionCommand/VehicalActionCommand
 * 2) Find MissionCommand or VehicalActionCommand for configured ID 
 * 3a) Either:
 *  - Re/Initialize waypoint manager
 *  - Send Mission commands based on AirVehicleState
 * 3b) Or:
 *  - If VehicalActionCommand commands a change in the vehicle's course, then suspend serving waypoints.
 *  - Send VehicalActionCommand command
 * 4) On command, resume serving waypoints
 * 
 * Configuration String: 
 *  <Service Type="WaypointPlanManagerService" NumberWaypointsToServe="100000" 
                    NumberWaypointsOverlap="3"  DefaultLoiterRadius_m="200.0"
                    TurnType="TurnShort" AddLoiterToEndOfSegments="FALSE" 
                    AddLoiterToEndOfMission="FALSE" LoopBackToFirstTask="FALSE" 
                    GimbalPayloadId="-1"/>
 * 
 * Options:
 *  - NumberWaypointsToServe
 *  - NumberWaypointsOverlap
 *  - DefaultLoiterRadius_m
 *  - AddLoiterToEndOfSegments
 *  - AddLoiterToEndOfMission
 *  - LoopBackToFirstTask
 *  - SetLastWaypointSpeedTo0
 *  - TurnType
 *  - GimbalPayloadId
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::AutomationResponse
 *  - afrl::cmasi::AirVehicleState
 *  - uxas::messages::uxnative::IncrementWaypoint
 *  - afrl::cmasi::MissionCommand
 * 
 * Sent Messages:
 *  - afrl::cmasi::MissionCommand
 * 
 */



class WaypointPlanManagerService : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("WaypointPlanManagerService");
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
        return new WaypointPlanManagerService;
    };

    WaypointPlanManagerService();

    virtual
    ~WaypointPlanManagerService();

private:

    static
    ServiceBase::CreationRegistrar<WaypointPlanManagerService> s_registrar;

    /** brief Copy construction not permitted */
    WaypointPlanManagerService(WaypointPlanManagerService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(WaypointPlanManagerService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    //bool
    //start() override;

    bool
    terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

protected:
    bool isInitializePlan(std::shared_ptr<afrl::cmasi::MissionCommand>& ptr_MissionCommand);
    bool isGetCurrentSegment(const int64_t& waypointIdCurrent, std::shared_ptr<avtas::lmcp::Object>& segmentCurrent, int64_t& idMissionSegmentCurrent);
    bool isGetNextWaypointId(const int64_t& waypointIdCurrent, int64_t& waypointIdNext);
    void setTurnType(const afrl::cmasi::TurnType::TurnType& turnType, std::shared_ptr<afrl::cmasi::MissionCommand>& ptr_MissionCommand);
    //void BuildCMASI_Waypoint(n_CMASI::Waypoint*& pWaypoint_Out, c_CmasiWaypointDistance::PTR_CMASI_WAYPOINT_t& ptr_Waypoint_In, const int& iNextWaypoint, const bool& bAddLoiter, const bool& bSetLastWaypointSpeedTo0);

    ////////////////////////
    // TIMER CALLBACKS
    /*! \brief timer callback for managing updating mission commands */
    void OnSendNewMissionTimer();

protected:

    /*! \brief  vector of mission commands for each segment in the full plan.*/
    std::vector< std::shared_ptr<afrl::cmasi::MissionCommand> > m_missionSegments;
    /*! \brief  ID of the current mission segment. This is the "CommandID" 
     * from the mission command.*/
    int64_t m_idMissionSegmentCurrent = {0};
    /*! \brief  ID of the vehicle that this manager is working for*/
    int64_t m_vehicleID = {-1}; // need a vehicle ID or can't do anything
    /*! \brief  number of waypoints to serve for each segment, up to the 
     * number available in the full plan.*/
    int32_t m_numberWaypointsToServe = {100000}; //serve them all
    /*! \brief  number of waypoints, before the last waypoint in the current
     * segment, to start the next segment*/
    int32_t m_numberWaypointOverlap = {3};
    /*! \brief  radius to use for loiters that are added by the waypoint manager*/
    double m_loiterRadiusDefault_m = {200.0};
    /*! \brief  add an infinite loiter to the each of set of waypoints (segment) served */
    bool m_isAddLoiterToEndOfSegments = {false};
    /*! \brief  add an infinite loiter to the last waypoint in the mission*/
    bool m_isAddLoiterToEndOfMission = {false};
    /*! \brief  use the index of the first waypoint with an associated task as the last waypoint in the mission's "NextWaypoint"*/
    bool m_isLoopBackToFirstTask = {false};
    /*! \brief  set the speed of the last waypoint in the mission to 0. Used for vehicles that should stop at end of plan*/
    bool m_isSetLastWaypointSpeedTo0 = {false};
    /*! \brief  received a :UXNATIVE:IncrementWaypoint message*/
    bool m_isMoveToNextWaypoint = {false};
    /*! \brief  this is the last "to" (destination) waypoint reported by the
     *  vehicle*/
    int64_t m_lastReportedToWaypoint = {-1};
    /*! \brief  the turn type to send out in mission commands*/
    afrl::cmasi::TurnType::TurnType _turnType = {afrl::cmasi::TurnType::TurnShort};
    /*! \brief  storage for the next mission command to send out*/
    std::shared_ptr<avtas::lmcp::Object> _nextMissionCommandToSend;
    /*! \brief  storage for the next mission command to send out*/
    uint64_t m_sendNewMissionTimerId{0};
    /*! \brief  minimun time between send in mission commands*/
    const int64_t _timeBetweenMissionCommandsMin_ms = {1000};
    /*! \brief  this is the payload Id to use for addressing the gimbal on the
     vehicle controlled by this manager*/
    int64_t m_gimbalPayloadId = {-1};

    /*! \brief  the state of the Rust implementation of WaypointPlanManager */
    void* m_WaypointPlanManager;

private:




};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_WAYPOINT_PLAN_MANAGER_SERVICE_H */


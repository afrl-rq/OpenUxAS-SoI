// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   OffRoadAttack.h
 * Author: steve
 *
 * Created on May 8, 2017, 5:55 PM
 */

#ifndef UXAS_OFF_ROAD_ATTACK_H
#define UXAS_OFF_ROAD_ATTACK_H


#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "TypeDefs/UxAS_TypeDefs_Timer.h"
#include <fstream>
#include "afrl/cmasi/MissionCommand.h"
namespace uxas
{
namespace service
{

/*! \class OffRoadAttack
 *\brief This is a basic example of a UxAS service that receives AirVehicleState
 * messages and sends camera pointing messages when videorecord messages are received. 
 * 
 * Configuration String:
 *  <Service Type="OffRoadAttack"/>
 * 
 * Subscribed Messages:
 *  - uxas.messages.uxnative.VideoRecord
 *  - afrl.cmasi.AirVehicleState
 * 
 * Sent Messages:
 *  - afrl.cmasi.GimbalStareAction
 * 
 */

class OffRoadAttack : public ServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="OffRoadAttack". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("OffRoadAttack");
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
        return new OffRoadAttack;
    };

    OffRoadAttack();

    virtual
    ~OffRoadAttack();

private:

    static
    ServiceBase::CreationRegistrar<OffRoadAttack> s_registrar;

    /** brief Copy construction not permitted */
    OffRoadAttack(OffRoadAttack const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(OffRoadAttack const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;
    bool isInitializePlan(std::shared_ptr<afrl::cmasi::MissionCommand>& ptr_MissionCommand);

    bool isGetCurrentSegment(const int64_t& waypointIdCurrent, std::shared_ptr<avtas::lmcp::Object>& segmentCurrent, int64_t& idMissionSegmentCurrent);
    bool isGetNextWaypointId(const int64_t& waypointIdCurrent, int64_t& waypointIdNext);
    void setTurnType(const afrl::cmasi::TurnType::TurnType& turnType, std::shared_ptr<afrl::cmasi::MissionCommand>& ptr_MissionCommand);
    void OnSendNewMissionTimer();
//    bool
//    initialize() override;
    bool
    initialize() override;
    
    bool
    start() override;
    
    bool
    terminate() override;
    
    private:
        bool m_isRecording{false};
        //__int64 RcvStateCount=0;
        //long start=0;
        long diffTime=0;
        std::ofstream myfile;
        int64_t m_vehicleID = {-1}; // need a vehicle ID or can't do anything
        
        /*! \brief  storage for the next mission command to send out*/
        std::shared_ptr<avtas::lmcp::Object> _nextMissionCommandToSend;  
        std::vector< std::shared_ptr<afrl::cmasi::MissionCommand> > m_missionSegments; 
        int64_t m_idMissionSegmentCurrent = {0};
        int64_t stateCount=0;
        int64_t m_lastReportedToWaypoint = {-1};
        afrl::cmasi::TurnType::TurnType _turnType = {afrl::cmasi::TurnType::TurnShort};
        int32_t m_numberWaypointsToServe = {100000}; //serve them all
        int32_t m_numberWaypointOverlap = {3};
        bool m_isAddLoiterToEndOfSegments = {false};
        bool m_isAddLoiterToEndOfMission = {false};
        bool m_isSetLastWaypointSpeedTo0 = {false};
        bool m_isMoveToNextWaypoint = {false};
        bool m_isLoopBackToFirstTask = {false};
        double m_loiterRadiusDefault_m = {200.0};
        int64_t m_gimbalPayloadId = {-1};
        uint64_t m_sendNewMissionTimerId{0};
        //attack at 80s
        int64_t _timeBetweenMissionCommandsMin_ms = {0};
        double attackFirstLat = {0};
        double attackFirstLon = {0};
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_OFF_ROAD_ATTACK_H */


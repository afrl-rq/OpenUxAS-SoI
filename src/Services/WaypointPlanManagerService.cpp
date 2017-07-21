// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_WaypointPlanManager.cpp
 * Author: steve
 *
 * Created on December 16, 2014, 4:47 PM
 *
 */


#include "WaypointPlanManagerService.h"

#include "UnitConversions.h"
#include "UxAS_TimerManager.h"

#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/GimbalAngleAction.h"
#include "afrl/cmasi/LoiterAction.h"
#include "uxas/messages/uxnative/IncrementWaypoint.h"

#include "pugixml.hpp"
#include "uxas/messages/task/TaskAutomationResponse.h"

#include <iostream>

extern "C" {
#include <zsrmvapi.h>
}

#define STRING_COMPONENT_NAME "WaypointPlanManager"

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_COMPONENT_TYPE "WaypointPlanManager"
#define STRING_XML_VEHICLE_ID "VehicleID"
#define STRING_XML_NUMBER_WAYPOINTS_TO_SERVE "NumberWaypointsToServe"
#define STRING_XML_NUMBER_WAYPOINTS_OVERLAP "NumberWaypointsOverlap"
#define STRING_XML_DEFAULT_LOITER_RADIUS_M "DefaultLoiterRadius_m"
#define STRING_XML_ADD_LOITER_TO_END_OF_SEGMENTS "AddLoiterToEndOfSegments"
#define STRING_XML_ADD_LOITER_TO_END_OF_MISSION "AddLoiterToEndOfMission"
#define STRING_XML_LOOP_BACK_TO_FIRST_TASK "LoopBackToFirstTask"
#define STRING_XML_SET_LAST_WAYPOINT_SPEED_TO_0 "SetLastWaypointSpeedTo0"
#define STRING_XML_TURN_TYPE "TurnType"
#define STRING_XML_GIMBAL_PAYLOAD_ID "GimbalPayloadId"

#define DEFAULT_SEGMENT_LENGTH_MIN_M (100000)
#define DEFAULT_NEW_WAYPOINTS_FRACTION (1.0)
#define DEFAULT_NUMBER_WAYPOINTS_MIN (-1)       // don't manage waypoints
#define DEFAULT_NUMBER_WAYPOINTS_MAX (100000)


#define COUT_INFO(MESSAGE) std::cout << "<>WaypointPlanManagerService:: " << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>WaypointPlanManagerService:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>WaypointPlanManagerService:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();


namespace uxas
{
namespace service
{
WaypointPlanManagerService::ServiceBase::CreationRegistrar<WaypointPlanManagerService>
WaypointPlanManagerService::s_registrar(WaypointPlanManagerService::s_registryServiceTypeNames());

WaypointPlanManagerService::WaypointPlanManagerService()
: ServiceBase(WaypointPlanManagerService::s_typeName(), WaypointPlanManagerService::s_directoryName()) 
{ 
    beginCloseBorder.setLongitude(-121.01294);
    beginCloseBorder.setLatitude(45.2898);
    endCloseBorder.setLongitude(-120.91681);
    endCloseBorder.setLatitude(45.32789);
    
    beginFarBorder.setLongitude(-121.0029);
    beginFarBorder.setLatitude(45.27694);
    endFarBorder.setLongitude(-120.906);
    endFarBorder.setLatitude(45.30954);
};

WaypointPlanManagerService::~WaypointPlanManagerService() { };

bool
WaypointPlanManagerService::configure(const pugi::xml_node& ndComponent)
{
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    bool bSucceeded(true);

    m_vehicleID = m_entityId; // can be overridden below

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();
    //assert(strComponentType==STRING_XML_COMPONENT_TYPE)

    if (!ndComponent.attribute(STRING_XML_VEHICLE_ID).empty())
    {
        m_vehicleID = ndComponent.attribute(STRING_XML_VEHICLE_ID).as_uint();
    }
    if (!ndComponent.attribute(STRING_XML_NUMBER_WAYPOINTS_TO_SERVE).empty())
    {
        m_numberWaypointsToServe = ndComponent.attribute(STRING_XML_NUMBER_WAYPOINTS_TO_SERVE).as_int();
    }
    if (!ndComponent.attribute(STRING_XML_NUMBER_WAYPOINTS_OVERLAP).empty())
    {
        m_numberWaypointOverlap = ndComponent.attribute(STRING_XML_NUMBER_WAYPOINTS_OVERLAP).as_int();
        if (m_numberWaypointOverlap < 2)
        {
            CERR_FILE_LINE_MSG("WARNING::WaypointPlanManagerService::bConfigure:: configuration overridden: m_numberWaypointOverlap set = 2. Configuration: [" << m_numberWaypointOverlap << "]")
            m_numberWaypointOverlap = 2;
        }
    }
    if (!ndComponent.attribute(STRING_XML_DEFAULT_LOITER_RADIUS_M).empty())
    {
        m_loiterRadiusDefault_m = ndComponent.attribute(STRING_XML_DEFAULT_LOITER_RADIUS_M).as_double();
    }
    if (!ndComponent.attribute(STRING_XML_ADD_LOITER_TO_END_OF_SEGMENTS).empty())
    {
        m_isAddLoiterToEndOfSegments = ndComponent.attribute(STRING_XML_ADD_LOITER_TO_END_OF_SEGMENTS).as_bool();
    }
    if (!ndComponent.attribute(STRING_XML_ADD_LOITER_TO_END_OF_MISSION).empty())
    {
        m_isAddLoiterToEndOfMission = ndComponent.attribute(STRING_XML_ADD_LOITER_TO_END_OF_MISSION).as_bool();
    }
    if (!ndComponent.attribute(STRING_XML_LOOP_BACK_TO_FIRST_TASK).empty())
    {
        m_isLoopBackToFirstTask = ndComponent.attribute(STRING_XML_LOOP_BACK_TO_FIRST_TASK).as_bool();
    }
    if (!ndComponent.attribute(STRING_XML_SET_LAST_WAYPOINT_SPEED_TO_0).empty())
    {
        m_isSetLastWaypointSpeedTo0 = ndComponent.attribute(STRING_XML_SET_LAST_WAYPOINT_SPEED_TO_0).as_bool();
    }
    if (!ndComponent.attribute(STRING_XML_TURN_TYPE).empty())
    {
        std::string turnTypeString = ndComponent.attribute(STRING_XML_TURN_TYPE).value();
        if (turnTypeString == "FlyOver")
        {
            _turnType = afrl::cmasi::TurnType::FlyOver;
        }
        else
        {
            _turnType = afrl::cmasi::TurnType::TurnShort;
        }
    }
    if (!ndComponent.attribute(STRING_XML_GIMBAL_PAYLOAD_ID).empty())
    {
        m_gimbalPayloadId = ndComponent.attribute(STRING_XML_GIMBAL_PAYLOAD_ID).as_int64();
    }

    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskAutomationResponse::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(uxas::messages::uxnative::IncrementWaypoint::Subscription);
    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription); // for direct implementation outside of automation response
    return (bSucceeded);
}

bool
WaypointPlanManagerService::initialize()
{
    bool bSuccess(true);

    // create and start periodic timer
    //m_sendNewMissionTimerId = uxas::common::TimerManager::getInstance().createTimer(
    //                                                                                std::bind(&WaypointPlanManagerService::OnSendNewMissionTimer, this), "WaypointPlanManagerService::OnSendNewMissionTimer");
    //uxas::common::TimerManager::getInstance().startPeriodicTimer(m_sendNewMissionTimerId, _timeBetweenMissionCommandsMin_ms, _timeBetweenMissionCommandsMin_ms);

    return (bSuccess);
};

bool
WaypointPlanManagerService::terminate()
{
    // stop timer
    uint64_t delayTime_ms{1000};
    if (m_sendNewMissionTimerId && !uxas::common::TimerManager::getInstance().destroyTimer(m_sendNewMissionTimerId, delayTime_ms))
    {
        UXAS_LOG_WARN("WaypointPlanManagerService::terminate failed to destroy new mission sender timer "
                 "(m_sendNewMissionTimerId) with timer ID ", m_sendNewMissionTimerId, " within ", delayTime_ms, " millisecond timeout");
    }
    return true;
}

bool firstTime = true;

bool
WaypointPlanManagerService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
//    afrl::cmasi::Waypoint beginBorder;
//    beginBorder.setLatitude(45.2898);
//    beginBorder.setLongitude(-121.01294);
//    afrl::cmasi::Waypoint endBorder;
//    endBorder.setLatitude(45.32789);
//    endBorder.setLongitude(-120.91681);

    //COUT_FILE_LINE_MSG("getLmcpTypeName()" << receivedLmcpMessage->m_object->getLmcpTypeName() << "]")
    std::shared_ptr<avtas::lmcp::Object> pMissionCommand_Out; // if a new mission command is generate it is saved in this variable

    if (receivedLmcpMessage->m_object->getLmcpTypeName() == "AirVehicleState")
    {
        afrl::cmasi::AirVehicleState* airVehicleState = static_cast<afrl::cmasi::AirVehicleState*> (receivedLmcpMessage->m_object.get());

        if (airVehicleState->getID() == m_vehicleID)
        {
            m_lastSafeReportedToWaypoint5 = m_lastSafeReportedToWaypoint4; 
            m_lastSafeReportedToWaypoint4 = m_lastSafeReportedToWaypoint3; 
            m_lastSafeReportedToWaypoint3 = m_lastSafeReportedToWaypoint2; 
            m_lastSafeReportedToWaypoint2 = m_lastSafeReportedToWaypoint1; 
            m_lastSafeReportedToWaypoint1 = m_lastSafeReportedToWaypoint; 
            m_lastSafeReportedToWaypoint = m_lastPrevReportedToWaypoint;
            m_lastPrevReportedToWaypoint = m_lastReportedToWaypoint;
            m_lastReportedToWaypoint = airVehicleState->getCurrentWaypoint();
            afrl::cmasi::Waypoint* wp= this->getWaypointFromID(m_lastReportedToWaypoint);            
            
            std::cout << "waypoint: " << m_lastReportedToWaypoint << "\n";
            
            if (!_stopped)
            {

                if (m_isMoveToNextWaypoint)
                {
                    int64_t waypointIdNext = {-1};
                    if (isGetNextWaypointId(airVehicleState->getCurrentWaypoint(), waypointIdNext))
                    {
                        int64_t idMissionSegmentTemp = {-1};
                        isGetCurrentSegment(waypointIdNext, _nextMissionCommandToSend, idMissionSegmentTemp);
                    }

                    m_isMoveToNextWaypoint = false;
                }
                else
                {
                    int64_t idMissionSegmentTemp = {-1};
                    isGetCurrentSegment(airVehicleState->getCurrentWaypoint(), _nextMissionCommandToSend, idMissionSegmentTemp);
                }

                if (wp != NULL) 
                {
                    // HERE: test this "impromptum correction with budget enforcement
                    if (!allowedWaypoint(beginCloseBorder,endCloseBorder,*wp) && _testing && isRuntimeAssuranceOn())
                    {
                        _testing = false;

                        // set new border to the close border 
                        // as a way to encode discovering a foe 
                        beginCurrentBorder = beginCloseBorder;
                        endCurrentBorder = endCloseBorder;
                        
                        // for now we just cause a big delay and do not send anything                        
                        std::cout << "Beyond border. Sleeping\n";
                        unsigned long long tsbuffer[10];
                        long bufsize=10;
                        long idx=0;
                        
                        if (!_temporalEnforcementActionActive){
                            // test with bad overrun -- disable enforcement signal -- was 15
                            busy_timestamped(1000, tsbuffer, bufsize, &idx);
                        } else {
                            // changed from 15
                            busy_timestamped(1000, tsbuffer, bufsize, &idx);                            
                        }
                                                
                        // clear the next command in order not to do anything
                        _nextMissionCommandToSend.reset();    
                        
                        if (!_temporalEnforcementActionActive){
                            // for testing we simulate a "stop" here
                            _stopped = true;
                        }
                    }
                }
            } else  // _stopped
            {
                // the budget enforcement stopped the vehicle
                // now we need to correct it and "resume"
                
                if (wp != NULL) 
                {
                    if (!allowedWaypoint(beginCurrentBorder,endCurrentBorder,*wp) && isRuntimeAssuranceOn())
                    {
                        auto cmd = getCurrentSegment(m_lastReportedToWaypoint);
                        
                        if (cmd)
                        {
                            correctSegment(cmd,beginCurrentBorder,endCurrentBorder);
                            cmd->setFirstWaypoint(m_lastReportedToWaypoint);
                            _nextMissionCommandToSend = cmd;
                        }
                    }
                }
                
                _stopped = false;
            }
        }
    }
    else if (afrl::cmasi::isAutomationResponse(receivedLmcpMessage->m_object.get()))
    {
        auto automationResponse = std::static_pointer_cast<afrl::cmasi::AutomationResponse> (receivedLmcpMessage->m_object);
        for (auto mission : automationResponse->getMissionCommandList())
        {
            if (mission->getVehicleID() == m_vehicleID)
            {
                //TODO:: initialize plan should initialize and get an initial plan
                std::shared_ptr<afrl::cmasi::MissionCommand> ptr_MissionCommand(mission->clone());
                if (isInitializePlan(ptr_MissionCommand))
                {
                    int64_t waypointIdCurrent = {ptr_MissionCommand->getWaypointList().front()->getNumber()};
                    int64_t idMissionSegmentTemp = {-1};
                    isGetCurrentSegment(waypointIdCurrent, _nextMissionCommandToSend, idMissionSegmentTemp);
                }
                break;
            }
        }
    }
    else if (uxas::messages::task::isTaskAutomationResponse(receivedLmcpMessage->m_object.get()))
    {
        auto taskautomationResponse = std::static_pointer_cast<uxas::messages::task::TaskAutomationResponse> (receivedLmcpMessage->m_object);
        auto automationResponse = taskautomationResponse->getOriginalResponse();
        for (auto mission : automationResponse->getMissionCommandList())
        {
            if (mission->getVehicleID() == m_vehicleID)
            {
                //TODO:: initialize plan should initialize and get an initial plan
                std::shared_ptr<afrl::cmasi::MissionCommand> ptr_MissionCommand(mission->clone());
                if (isInitializePlan(ptr_MissionCommand))
                {
                    int64_t waypointIdCurrent = {ptr_MissionCommand->getWaypointList().front()->getNumber()};
                    int64_t idMissionSegmentTemp = {-1};
                    isGetCurrentSegment(waypointIdCurrent, _nextMissionCommandToSend, idMissionSegmentTemp);
                }
                break;
            }
        }
    }
    else if (receivedLmcpMessage->m_object->getLmcpTypeName() == "MissionCommand")
    {
        if (static_cast<afrl::cmasi::MissionCommand*> (receivedLmcpMessage->m_object.get())->getVehicleID() == m_vehicleID)
        {
            //TODO:: initialize plan should intialize and get an std::string(n_Const::c_Constant_Strings::strGetPrepend_lmcp() + ":UXNATIVE:IncrementWaypoint")intial plan
            std::shared_ptr<afrl::cmasi::MissionCommand> ptr_MissionCommand(static_cast<afrl::cmasi::MissionCommand*> (receivedLmcpMessage->m_object.get())->clone());
            if (isInitializePlan(ptr_MissionCommand))
            {
                int64_t waypointIdCurrent = {ptr_MissionCommand->getWaypointList().front()->getNumber()};
                int64_t idMissionSegmentTemp = {-1};
                if (isGetCurrentSegment(waypointIdCurrent, _nextMissionCommandToSend, idMissionSegmentTemp))
                {
                    if (idMissionSegmentTemp >= 0)
                    {
                        m_idMissionSegmentCurrent = idMissionSegmentTemp;
                    }
                }
            }
        }
        //sendSharedLmcpObjectBroadcastMessage(ptr_odstObjectDestination->ptrGetObject());
    }
    else if (receivedLmcpMessage->m_object->getLmcpTypeName() == "VehicleActionCommand")
    {
        //TODO:: send out to vehicle
    }
#ifdef STEVETEST
    else if (receivedLmcpMessage->m_object->getLmcpTypeName() == "IncrementWaypoint")
    {
        uxas::messages::uxnative::IncrementWaypoint* incrementWaypoint = static_cast<uxas::messages::uxnative::IncrementWaypoint*> (receivedLmcpMessage->m_object.get());

        if (incrementWaypoint->getEntityID() == m_vehicleID)
        {
            CERR_FILE_LINE_MSG("Received IncrementWaypoint!!!!!")
            m_isMoveToNextWaypoint = true;
        }
        incrementWaypoint = nullptr; //don't own this
    }
#endif  //STEVETEST
    else
    {
        //CERR_FILE_LINE_MSG("WARNING:: Unknown message encountered: [" << receivedLmcpMessage->m_object->getLmcpTypeName() << "]")
    }
    
    if(_nextMissionCommandToSend)
    {
        if (firstTime && isRuntimeAssuranceOn())
        {
            firstTime = false;
            static_cast<afrl::cmasi::MissionCommand*>(_nextMissionCommandToSend.get())->setFirstWaypoint(100004040);
        }
        sendSharedLmcpObjectBroadcastMessage(_nextMissionCommandToSend);
        _nextMissionCommandToSend.reset();
    }
    
    return (false); // always false implies never terminating service from here
};

void
WaypointPlanManagerService::aroundFoes(const afrl::cmasi::Waypoint &startBorder, const afrl::cmasi::Waypoint &endBorder,afrl::cmasi::Waypoint& wp)
{   
}

void
WaypointPlanManagerService::safeStop()
{
    afrl::cmasi::Waypoint* wp;
    afrl::cmasi::MissionCommand *cmd = new afrl::cmasi::MissionCommand();
    
    if (m_lastReportedToWaypoint >=0)
    {
        wp = this->getWaypointFromID(m_lastReportedToWaypoint-2);
        if (wp != NULL)
        {            
            afrl::cmasi::LoiterAction * pLoiterAction(new afrl::cmasi::LoiterAction());
            pLoiterAction->setRadius(100);//m_loiterRadiusDefault_m);
            pLoiterAction->setDuration(-1);
            pLoiterAction->setAirspeed(wp->getSpeed());
            afrl::cmasi::Location3D* pLocation3D = new afrl::cmasi::Location3D();
            pLocation3D->setLatitude(wp->getLatitude());
            pLocation3D->setLongitude(wp->getLongitude());
            pLocation3D->setAltitude(wp->getAltitude());
            pLoiterAction->setLocation(pLocation3D);
            pLocation3D = 0; //don't own
            
            wp = wp->clone();
            wp->getVehicleActionList().clear();
            wp->getVehicleActionList().push_back(pLoiterAction);
            wp->setNextWaypoint(wp->getNumber());
            cmd->setCommandID(1);
            cmd->setFirstWaypoint(wp->getNumber());
            cmd->getWaypointList().push_back(wp);
            cmd->setVehicleID(m_vehicleID);
            _stopMissionCommandToSend.reset(cmd);
            sendSharedLmcpObjectBroadcastMessage(_stopMissionCommandToSend);
            //_stopMissionCommandToSend.reset();
        }
    }
}

/*********************************************************************/
//-- this method performs logical enforcement and sends out a set of
//-- waypoints that are safe to be followed.
/*********************************************************************/
void
WaypointPlanManagerService::rta_sendSharedLmcpObjectBroadcastMessage
(const std::shared_ptr<avtas::lmcp::Object>& lmcpObject)
{

    //-- get the next set of waypoints created by the service
    auto missionCmd = static_cast<afrl::cmasi::MissionCommand *>(lmcpObject.get());
    std::vector<afrl::cmasi::Waypoint*> &wpl = missionCmd->getWaypointList();

    //-- project all unsafe waypoints on to the border
    for (size_t i=0;i<wpl.size();i++)
    {
        //-- if this waypoint is in the unsafe zone, project it on the
        //-- border
        if(!allowedWaypoint(beginCurrentBorder,endCurrentBorder,*(wpl[i])))
            projectWayPoint(beginCurrentBorder,endCurrentBorder,*(wpl[i]));
    }

    sendSharedLmcpObjectBroadcastMessage(lmcpObject);
}

/*********************************************************************/
//-- return true if the last argument is on the "positive" side of the
//-- border defined by the first two points.
/*********************************************************************/
bool
WaypointPlanManagerService::allowedWaypoint(const afrl::cmasi::Waypoint &startBorder,
                                            const afrl::cmasi::Waypoint &endBorder,
                                            const afrl::cmasi::Waypoint &wp)
{
    double x1 = startBorder.getLatitude();
    double y1 = startBorder.getLongitude();
    double x2 = endBorder.getLatitude();
    double y2 = endBorder.getLongitude();
    double x = wp.getLatitude();
    double y = wp.getLongitude();
    
    return (((x-x1)*(y2-y1)-(y-y1)*(x2-x1)) > 0);
}

/*********************************************************************/
//-- project the third point on to the border defined by the first two
//-- points. the third point is changed as a side effect.
/*********************************************************************/
void
WaypointPlanManagerService::projectWayPoint(const afrl::cmasi::Waypoint &startBorder,
                                            const afrl::cmasi::Waypoint &endBorder,
                                            afrl::cmasi::Waypoint &wp)
{
    double x1 = startBorder.getLatitude();
    double y1 = startBorder.getLongitude();
    double x2 = endBorder.getLatitude();
    double y2 = endBorder.getLongitude();
    double x = wp.getLatitude();
    double y = wp.getLongitude();

    //-- border endpoints have same latitude
    if(x1 == x2)
    {
        wp.setLatitude(x1);
        return;
    }

    //-- border endpoints have same longitude
    if(y1 == y2)
    {
        wp.setLongitude(y1);
        return;
    }

    //-- otherwise solve equations y = m1.x+c1 and y = m2.x+c2
    double m1 = (y2 - y1) / (x2 -x1);
    double m2 = -1.0 / m1;
    double c2 = y - m2 * x;
    double c1 = y1 - m1 * x1;

    double yp = (c1*m2 - c2*m1) / (m2 - m1);
    double xp = (yp - c1) / m1;
    wp.setLatitude(xp);
    wp.setLongitude(yp);
}

void WaypointPlanManagerService::zs_budget_enforcement_handler(int rid)
{  
//    afrl::cmasi::Waypoint beginBorder;
//    beginBorder.setLatitude(45.2898);
//    beginBorder.setLongitude(-121.01294);
//    afrl::cmasi::Waypoint endBorder;
//    endBorder.setLatitude(45.32789);
//    endBorder.setLongitude(-120.91681);

    std::cout << "Budget enforcement rid("<<rid<<"): tid("<<gettid()<<")";
    if (isRuntimeAssuranceOn() && _temporalEnforcementActionActive)
    {
        std::cout<< "Runtime Assurance ACTIVE: ";
        if (!_stopped){
            std::cout << "stopping!";
            _stopped = true;
            safeStop();
        }

//        if (m_lastReportedToWaypoint >=0)
//        {
//            afrl::cmasi::Waypoint* wp= getWaypointFromID(m_lastReportedToWaypoint);            
//            if (wp != NULL) 
//            {
//                if (!allowedWaypoint(beginBorder,endBorder,*wp))
//                {
//                    //_nextMissionCommandToSend.reset();
//                    if (!_stopped){
//                        std::cout << "stopping!";
//                        _stopped = true;
//                        safeStop();
//                    }
//                }
//            }
//        }
    }
    else
    {
        std::cout << "Runtime Assurance NOT ACTIVE";
    }
    std::cout << "\n";
}

bool WaypointPlanManagerService::isInitializePlan(std::shared_ptr<afrl::cmasi::MissionCommand> & ptr_MissionCommand)
{
    bool isSucceeded(true);

    if (m_vehicleID > 0)
    {
        m_lastReportedToWaypoint = -1;

        //******* build a new container of mission segments*******
        m_missionSegments.clear();

        if (!ptr_MissionCommand->getWaypointList().empty())
        {
            setTurnType(_turnType, ptr_MissionCommand);

            // setup a template for the mission commands
            std::shared_ptr<afrl::cmasi::MissionCommand> missionCommandTemp(new afrl::cmasi::MissionCommand);
            missionCommandTemp->setVehicleID(m_vehicleID);
            missionCommandTemp->setStatus(afrl::cmasi::CommandStatusType::Approved);
            //missionCommandTemp->setStatus(afrl::cmasi::CommandStatusType::InProcess);
            missionCommandTemp->setFirstWaypoint(-1); // uninitialized

            std::shared_ptr<afrl::cmasi::MissionCommand> missionSegment_01(missionCommandTemp->clone());
            missionSegment_01->setCommandID(getUniqueEntitySendMessageId());
            //COUT_INFO("missionSegment_01->getCommandID[" << missionSegment_01->getCommandID() << "]")

            std::shared_ptr<afrl::cmasi::MissionCommand> missionSegment_02(missionCommandTemp->clone());
            missionSegment_02->setCommandID(getUniqueEntitySendMessageId());
            //COUT_INFO("missionSegment_02->getCommandID[" << missionSegment_01->getCommandID() << "]")

            auto itWaypoint = ptr_MissionCommand->getWaypointList().begin();
            for (; itWaypoint != ptr_MissionCommand->getWaypointList().end(); itWaypoint++)
            {
                if (missionSegment_01->getWaypointList().size() < static_cast<size_t>(m_numberWaypointsToServe))
                {
                    missionSegment_01->getWaypointList().push_back((*itWaypoint)->clone());
                    // check for overlap
                    if ((m_numberWaypointsToServe - missionSegment_01->getWaypointList().size()) < static_cast<size_t>(m_numberWaypointOverlap))
                    {
                        missionSegment_02->getWaypointList().push_back((*itWaypoint)->clone());
                    }

                    // commanded first waypoint is the second one in the plan, unless there is only one waypoint
                    if (missionSegment_01->getWaypointList().size() <= 2)
                    {
                        missionSegment_01->setFirstWaypoint((*itWaypoint)->getNumber());
                    }
                    if (missionSegment_02->getWaypointList().size() <= 2)
                    {
                        missionSegment_02->setFirstWaypoint((*itWaypoint)->getNumber());
                    }
                }
                else
                {
                    missionSegment_02->getWaypointList().push_back((*itWaypoint)->clone());
                    if (missionSegment_01->getFirstWaypoint() >= 0)
                    {
                        if (m_isAddLoiterToEndOfSegments)
                        {
                            afrl::cmasi::Waypoint* waypointCurrent = missionSegment_01->getWaypointList().back();
                            afrl::cmasi::LoiterAction * pLoiterAction(new afrl::cmasi::LoiterAction());
                            pLoiterAction->setRadius(m_loiterRadiusDefault_m);
                            pLoiterAction->setDuration(-1);
                            pLoiterAction->setAirspeed(waypointCurrent->getSpeed());
                            afrl::cmasi::Location3D* pLocation3D = new afrl::cmasi::Location3D();
                            pLocation3D->setLatitude(waypointCurrent->getLatitude());
                            pLocation3D->setLongitude(waypointCurrent->getLongitude());
                            pLocation3D->setAltitude(waypointCurrent->getAltitude());
                            pLoiterAction->setLocation(pLocation3D);
                            pLocation3D = 0; //don't own
                            waypointCurrent->getVehicleActionList().push_back(pLoiterAction);
                            pLoiterAction = 0; //don't own it
                            waypointCurrent = 0; //don't own it
                        }
                        m_missionSegments.push_back(missionSegment_01);
                        missionSegment_01 = missionSegment_02;
                        missionSegment_02.reset(missionCommandTemp->clone());
                        missionSegment_02->setCommandID(getUniqueEntitySendMessageId());
                        //COUT_INFO("missionSegment_02->getCommandID[" << missionSegment_01->getCommandID() << "]")
                    }
                    else
                    {
                        CERR_FILE_LINE_MSG("ERROR::WaypointPlanManagerService::isInitializePlan:: first waypoint of segment was not set!!!!")
                        isSucceeded = false;
                    }
                }
            } //for (auto itWaypoint=ptr_MissionCommand->getWaypointList() .....
            if (missionSegment_01->getFirstWaypoint() >= 0)
            {
                // final segment
                m_missionSegments.push_back(missionSegment_01);
            }
            if (!m_missionSegments.empty())
            {
#ifdef STEVETEST
                // disassociate the last waypoint in the mission from the tasks, allows tasks to complete
                afrl::cmasi::Waypoint* waypointCurrent = m_missionSegments.back()->getWaypointList().back()->clone();
                auto newNumber = waypointCurrent->getNumber() + 1;
                waypointCurrent->setNumber(newNumber);
                waypointCurrent->setNextWaypoint(newNumber);
                m_missionSegments.back()->getWaypointList().back()->setNextWaypoint(newNumber);
                waypointCurrent->getAssociatedTasks().clear();

                m_missionSegments.back()->getWaypointList().push_back(waypointLast);
#else
                afrl::cmasi::Waypoint* waypointLast = m_missionSegments.back()->getWaypointList().back();
#endif  //#endif  //STEVETEST

                if (m_isAddLoiterToEndOfMission)
                {
                    afrl::cmasi::LoiterAction * pLoiterAction(new afrl::cmasi::LoiterAction());
                    pLoiterAction->setRadius(m_loiterRadiusDefault_m);
                    pLoiterAction->setDuration(-1);
                    if (m_isSetLastWaypointSpeedTo0)
                    {
                        pLoiterAction->setAirspeed(0);
                    }
                    {
                        pLoiterAction->setAirspeed(waypointLast->getSpeed());
                    }
                    afrl::cmasi::Location3D* pLocation3D = new afrl::cmasi::Location3D();
                    pLocation3D->setLatitude(waypointLast->getLatitude());
                    pLocation3D->setLongitude(waypointLast->getLongitude());
                    pLocation3D->setAltitude(waypointLast->getAltitude());
                    pLoiterAction->setLocation(pLocation3D);
                    pLocation3D = 0; //don't own
                    waypointLast->getVehicleActionList().push_back(pLoiterAction);
                    pLoiterAction = 0; //don't own it
                }

                if (m_gimbalPayloadId > 0)
                {
                    // point the camera out in front of the vehicle
                    auto pGimbalAngleAction = new afrl::cmasi::GimbalAngleAction();
                    pGimbalAngleAction->setPayloadID(m_gimbalPayloadId);
                    pGimbalAngleAction->setElevation(-60.0);
                    waypointLast->getVehicleActionList().push_back(pGimbalAngleAction);
                    pGimbalAngleAction = nullptr;
                }

                if (m_isSetLastWaypointSpeedTo0)
                {
                    waypointLast->setSpeed(0);
                }

                if (m_isLoopBackToFirstTask)
                {
                    waypointLast->setNextWaypoint(m_missionSegments.front()->getWaypointList().front()->getNumber());
                }

                waypointLast = 0; //don't own it
            }
            else
            {
                CERR_FILE_LINE_MSG("ERROR::WaypointPlanManagerService::isInitializePlan:: no m_missionSegments constructed from the MissionCommand!!!!")
                isSucceeded = false;
            }
        }
        else
        {
            CERR_FILE_LINE_MSG("ERROR::WaypointPlanManagerService::isInitializePlan:: no waypoints found in the MissionCommand!!!!")
            isSucceeded = false;
        }
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::WaypointPlanManagerService::isInitializePlan:: vehicle ID not > 0!!!!")
        isSucceeded = false;
    }
    return (isSucceeded);
};

afrl::cmasi::Waypoint* 
WaypointPlanManagerService::getWaypointFromID(const int64_t& waypointIdCurrent)
{
    for (auto itSegment = m_missionSegments.begin(); itSegment != m_missionSegments.end(); itSegment++)
    {
        for (auto itWaypoint = (*itSegment)->getWaypointList().begin(); itWaypoint != (*itSegment)->getWaypointList().end(); itWaypoint++)
        {
            if ((*itWaypoint)->getNumber() == waypointIdCurrent)
            {
                return *itWaypoint;
            }
        }
    }
    return NULL;
}

std::shared_ptr<afrl::cmasi::MissionCommand>
WaypointPlanManagerService::getCurrentSegment(const int64_t& waypointIdCurrent)
{
    for (auto itSegment : m_missionSegments)
    {
        for (auto itWaypoint : itSegment->getWaypointList())
        {
            if (itWaypoint->getNumber() == waypointIdCurrent)
            {
                return itSegment;
            }
        }
    }    
    return NULL;
}

void
WaypointPlanManagerService::correctSegment(std::shared_ptr<afrl::cmasi::MissionCommand> segment, afrl::cmasi::Waypoint &startBorder,afrl::cmasi::Waypoint &endBorder)
{    
    for (auto itWaypoint : segment->getWaypointList())
    {
        if (!allowedWaypoint(startBorder,endBorder,*itWaypoint))
        {
            projectWayPoint(startBorder,endBorder,*itWaypoint);
        }
    }
}

bool WaypointPlanManagerService::isGetCurrentSegment(const int64_t& waypointIdCurrent, std::shared_ptr<avtas::lmcp::Object>& segmentCurrent, int64_t & idMissionSegmentCurrent)
{
    bool isSucceeded(false);

    // return segment in segmentCurrent. does not change segmentCurrent if a segment is not found or is already current
    // if a pointer is generated, this function gives up ownership on return

    // search through all of the segments and find the last segment with this waypointID
    std::shared_ptr<afrl::cmasi::MissionCommand> segmentTemp;
    for (auto itSegment = m_missionSegments.begin(); itSegment != m_missionSegments.end(); itSegment++)
    {
        for (auto itWaypoint = (*itSegment)->getWaypointList().begin(); itWaypoint != (*itSegment)->getWaypointList().end(); itWaypoint++)
        {
            if ((*itWaypoint)->getNumber() == waypointIdCurrent)
            {
                // if possible, don't choose a segment where the desired waypoint is first, unless it is the first segment
                if ((itWaypoint != (*itSegment)->getWaypointList().begin()) || (!segmentTemp)) // not first waypoint in the segment OR (not yet found))
                {
                    segmentTemp = *itSegment;
                }
                //break;
            }
        }
    }

    if (segmentTemp && (segmentTemp->getCommandID() != m_idMissionSegmentCurrent))
    {
        COUT_INFO("New Segment: m_idMissionSegmentNew[" << segmentTemp->getCommandID() << "] m_idMissionSegmentOld[" << m_idMissionSegmentCurrent << "] waypointIdCurrent[" << waypointIdCurrent << "] First Segment Waypoint[" << segmentTemp->getWaypointList().front()->getNumber() << "] Last[" << segmentTemp->getWaypointList().back()->getNumber() << "]")
        m_idMissionSegmentPrev = m_idMissionSegmentCurrent;
        m_idMissionSegmentCurrent = segmentTemp->getCommandID();
        afrl::cmasi::MissionCommand* segmentCurrentLocal = {segmentTemp->clone()};
        idMissionSegmentCurrent = segmentCurrentLocal->getCommandID();

        // don't "goto" the first waypoint in the segment as the first waypoint to go to
        // this is set as the second waypoint in the segment by default
        if (waypointIdCurrent != segmentCurrentLocal->getWaypointList().front()->getNumber())
        {
            segmentCurrentLocal->setFirstWaypoint(waypointIdCurrent);
        }
        segmentCurrent.reset(segmentCurrentLocal);
        segmentCurrentLocal = nullptr;
        isSucceeded = true;
    }

    return (isSucceeded);
}

bool WaypointPlanManagerService::isGetNextWaypointId(const int64_t& waypointIdCurrent, int64_t & waypointIdNext)
{
    bool isSucceeded(false);

    for (auto itSegment = m_missionSegments.begin(); itSegment != m_missionSegments.end(); itSegment++)
    {
        bool isFoundCurrent = {false};
        for (auto itWaypoint = (*itSegment)->getWaypointList().begin(); itWaypoint != (*itSegment)->getWaypointList().end(); itWaypoint++)
        {
            if ((*itWaypoint)->getNumber() == waypointIdCurrent)
            {
                isFoundCurrent = true;
            }
            else if (isFoundCurrent)
            {
                waypointIdNext = (*itWaypoint)->getNumber();
                isSucceeded = true;
                break;
            }
        }
    }

    return (isSucceeded);
}

void WaypointPlanManagerService::setTurnType(const afrl::cmasi::TurnType::TurnType& turnType, std::shared_ptr<afrl::cmasi::MissionCommand> & ptr_MissionCommand)
{
    for (auto itWaypoint = ptr_MissionCommand->getWaypointList().begin();
            itWaypoint != ptr_MissionCommand->getWaypointList().end();
            itWaypoint++)
    {
        (*itWaypoint)->setTurnType(turnType);
    }
}

void WaypointPlanManagerService::OnSendNewMissionTimer()
{
    if (_nextMissionCommandToSend)
    {
        sendSharedLmcpObjectBroadcastMessage(_nextMissionCommandToSend);
        _nextMissionCommandToSend.reset();
    }
}

}; //namespace service
}; //namespace uxas

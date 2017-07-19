// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   BackToBeginAttack
 * Author: steve
 *
 * Created on May 8, 2017, 5:55 PM
 *
 * <Service Type="BackToBeginAttack" StringToSend="Option_01" SendPeriod_ms="36" />
 * 
 */

// include header for this service
#include "BackToBeginAttack.h"

#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/GimbalAngleAction.h"
#include "uxas/messages/uxnative/VideoRecord.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/impact/ImpactLineSearchTask.h"
#include "afrl/impact/ImpactPointSearchTask.h"
#include "uxas/messages/task/AssignmentCostMatrix.h"
#include "uxas/messages/task/TaskAssignmentSummary.h"
#include "uxas/messages/task/TaskPlanOptions.h"
#include "uxas/messages/task/TaskImplementationRequest.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/route/RoutePlanResponse.h"
#include "uxas/messages/route/RoutePlanRequest.h"
#include "uxas/messages/uxnative/IncrementWaypoint.h"
#include "UxAS_TimerManager.h"
// print outs
#include <iostream>     // std::cout, cerr, etc
#include <chrono>

#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>BackToBeginAttack:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define STRING_XML_VEHICLE_ID "VehicleID"
#define STRING_TIME_BETWEEN_MISSION_COMMANDS_MS "TimeBetweenMissionCommandsMin_ms"
#define STRING_XML_NUMBER_WAYPOINTS_TO_SERVE "NumberWaypointsToServe"
#define COUT_INFO(MESSAGE) std::cout << "<>!!!BackToBeginAttack:: " << MESSAGE << std::endl;std::cout.flush();
// namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{

// this entry registers the service in the service creation registry
BackToBeginAttack::ServiceBase::CreationRegistrar<BackToBeginAttack>
BackToBeginAttack::s_registrar(BackToBeginAttack::s_registryServiceTypeNames());

// service constructor
BackToBeginAttack::BackToBeginAttack()
: ServiceBase(BackToBeginAttack::s_typeName(), BackToBeginAttack::s_directoryName()) { };

// service destructor
BackToBeginAttack::~BackToBeginAttack() { };


bool BackToBeginAttack::configure(const pugi::xml_node& ndComponent)
{
    uint32_t ui32EntityID = m_entityId;
    
    bool isSuccess(true);
    m_vehicleID = m_entityId; // can be overridden below
    
    if (!ndComponent.attribute(STRING_XML_VEHICLE_ID).empty())
    {
        m_vehicleID = ndComponent.attribute(STRING_XML_VEHICLE_ID).as_uint();
        //two IDs, 400 and 500 will be printed out respectively
        //for each vehicle, it has its own m_vehicleID, m_numberWaypointsToServe......
        //WaypointPlanManagerSerive will fetch all the vehicle 400 information first and then do vehicle 500
//        std::cout << "my debug:" << std::endl;
//        std::cout << m_vehicleID << std::endl;
    }
    
        if (!ndComponent.attribute(STRING_TIME_BETWEEN_MISSION_COMMANDS_MS).empty())
    {
        _timeBetweenMissionCommandsMin_ms = ndComponent.attribute(STRING_TIME_BETWEEN_MISSION_COMMANDS_MS).as_uint();
        //two IDs, 400 and 500 will be printed out respectively
        //for each vehicle, it has its own m_vehicleID, m_numberWaypointsToServe......
        //WaypointPlanManagerSerive will fetch all the vehicle 400 information first and then do vehicle 500
//        std::cout << "my debug:" << std::endl;
//        std::cout << m_vehicleID << std::endl;
    }
        if (!ndComponent.attribute(STRING_XML_NUMBER_WAYPOINTS_TO_SERVE).empty())
    {
        m_numberWaypointsToServe = ndComponent.attribute(STRING_XML_NUMBER_WAYPOINTS_TO_SERVE).as_int();
    }
    
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(uxas::messages::uxnative::VideoRecord::Subscription);
    addSubscriptionAddress(afrl::cmasi::GimbalStareAction::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
    
    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    
    // subscribe to task plan options to build matrix
    addSubscriptionAddress(uxas::messages::task::TaskPlanOptions::Subscription);
    
    addSubscriptionAddress(uxas::messages::task::AssignmentCostMatrix::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskAssignmentSummary::Subscription);
    addSubscriptionAddress(uxas::messages::route::RoutePlanResponse::Subscription);
    addSubscriptionAddress(uxas::messages::route::RoutePlanRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskImplementationRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskImplementationResponse::Subscription);

    
    //fetch the first "Type" element in configuration file, which is "BackToBeginAttack"
    std::string strComponentType = ndComponent.attribute("Type").value();
    std::cout << strComponentType << std::endl;

    //
    return (isSuccess);
}

bool
BackToBeginAttack::initialize()
{
    bool bSuccess(true);

    // create and start periodic timer, time interval between two command message is 1000ms
    m_sendNewMissionTimerId = uxas::common::TimerManager::getInstance().createTimer(
                                                                                    std::bind(&BackToBeginAttack::OnSendNewMissionTimer, this), "BackToBeginAttack::OnSendNewMissionTimer");
    uxas::common::TimerManager::getInstance().startPeriodicTimer(m_sendNewMissionTimerId, _timeBetweenMissionCommandsMin_ms, _timeBetweenMissionCommandsMin_ms);

    return (bSuccess);
};

bool BackToBeginAttack::start()
{
    // perform any actions required at the time the service starts
    
    myfile.open ("msgLog.txt", std::ios::app);
    return (true);
};

bool BackToBeginAttack::terminate()
{
    std::cout << "myfile is closed" << std::endl;
    myfile.close();
    
    // stop timer
    return true;
}

bool BackToBeginAttack::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    std::shared_ptr<avtas::lmcp::Object> messageObject = receivedLmcpMessage->m_object;
    
    if(afrl::cmasi::isAirVehicleState(messageObject.get())){
        stateCount++;
        //if diffTime is around 10 ms, that means the state is for next UAV
//        diffTime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count()-start;
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        //check if UAVs are periodically reporting their states.
        afrl::cmasi::AirVehicleState* airVehicleState = static_cast<afrl::cmasi::AirVehicleState*> (messageObject.get());
        std::string msgName = airVehicleState->getFullLmcpTypeName();
        //m_vehicleID= airVehicleState->getID();//wrong, cannot assign m_vehicleID like this

        //std::cout << "airVehicleState msg received" << std::endl;
        myfile << currentTimeStamp << "   " << m_vehicleID << "   " << msgName << "\n";
        
        
        if (airVehicleState->getID() == m_vehicleID)
        {
            //in initialization phase, m_isMoveToNextWaypoint is still false, in execution phase, it is true
            //In execution phase
            ////never true!! shit
            if (m_isMoveToNextWaypoint)
            {
                int64_t waypointIdNext = {-1};
                if (isGetNextWaypointId(airVehicleState->getCurrentWaypoint(), waypointIdNext))
                {
                    int64_t idMissionSegmentTemp = {-1};
                    //std::cout << "I am true" << std::endl;
                    isGetCurrentSegment(waypointIdNext, _nextMissionCommandToSend, idMissionSegmentTemp);
                }

                m_isMoveToNextWaypoint = false;
            }
            // then it is in initialization phase
//            else
//            {
//                //std::cout << "I am in else" << std::endl;
//                int64_t idMissionSegmentTemp = {-1};
//                isGetCurrentSegment(airVehicleState->getCurrentWaypoint(), _nextMissionCommandToSend, idMissionSegmentTemp);
//            }
//            if(stateCount== 400)
//            {
//                std::cout << "stateCount is 400" << std::endl;
//                OnSendNewMissionTimer();
//            }
        }
    }
    
    else if(afrl::cmasi::isAirVehicleConfiguration(messageObject.get())){
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        afrl::cmasi::AirVehicleConfiguration* airVehicleConfiguration = static_cast<afrl::cmasi::AirVehicleConfiguration*> (messageObject.get());
        std::string msgName = airVehicleConfiguration->getFullLmcpTypeName();
        
        //std::cout << "airVehicleConfiguration msg received" << std::endl;
        myfile << currentTimeStamp << "   " << m_vehicleID << "   " << msgName << "\n";
    }
    
    else if(uxas::messages::uxnative::isVideoRecord(messageObject.get())){
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        uxas::messages::uxnative::VideoRecord* videoRecord = static_cast<uxas::messages::uxnative::VideoRecord*> (messageObject.get());
        std::string msgName = videoRecord->getFullLmcpTypeName();
        bool videoAction = videoRecord->getRecord();
        
        //std::cout << "video msg received" << std::endl;
        myfile << currentTimeStamp << "   " << m_vehicleID << "   " << msgName << "   " << videoAction << "\n";
    }
    
    
    else if (afrl::cmasi::isMissionCommand(messageObject.get()))
    {
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        auto missionCmd = std::static_pointer_cast<afrl::cmasi::MissionCommand>(messageObject);
        int64_t VehicleID = missionCmd->getVehicleID();
        std::string msgName = missionCmd->getFullLmcpTypeName();
        
        std::cout << "MissionCommand received" << std::endl;
        myfile << currentTimeStamp << "   " << VehicleID << "   " << msgName << "\n";
//        if (static_cast<afrl::cmasi::MissionCommand*> (receivedLmcpMessage->m_object.get())->getVehicleID() == m_vehicleID)
//        {
//            //TODO:: initialize plan should intialize and get an std::string(n_Const::c_Constant_Strings::strGetPrepend_lmcp() + ":UXNATIVE:IncrementWaypoint")intial plan
//            std::shared_ptr<afrl::cmasi::MissionCommand> ptr_MissionCommand(static_cast<afrl::cmasi::MissionCommand*> (receivedLmcpMessage->m_object.get())->clone());
//            if (isInitializePlan(ptr_MissionCommand))
//            {
//                int64_t waypointIdCurrent = {ptr_MissionCommand->getWaypointList().front()->getNumber()};
//                int64_t idMissionSegmentTemp = {-1};
//                if (isGetCurrentSegment(waypointIdCurrent, _nextMissionCommandToSend, idMissionSegmentTemp))
//                {
//                    if (idMissionSegmentTemp >= 0)
//                    {
//                        m_idMissionSegmentCurrent = idMissionSegmentTemp;
//                    }
//                }
//            }
//        }
    }   
    
    else if (afrl::cmasi::isAutomationResponse(messageObject.get()))
    {
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        auto response = std::static_pointer_cast<afrl::cmasi::AutomationResponse>(messageObject);
        
        //-10 means this response does not require vehicle id
        std::string VehicleID = "nul";
        std::string msgName = response->getFullLmcpTypeName();
        std::cout << "AutomationResponse received" << std::endl;
        myfile << currentTimeStamp << "   " << VehicleID << "   " << msgName << "\n";
        
        auto automationResponse = std::static_pointer_cast<afrl::cmasi::AutomationResponse> (receivedLmcpMessage->m_object);
        long listSize = automationResponse->getMissionCommandList().size();
        ////assign mission to ptr_MissionCommand, ptr_MissionCommand will be assigned to m_missionSegments 
        //for waterway example, size is 1
        //receive only one automationResponse 
        for (auto mission : automationResponse->getMissionCommandList())
        {
            //two vehicles in total, but only one id will match the mission vehicle id and satisfied this check
            if (mission->getVehicleID() == m_vehicleID)
            {
                //TODO:: initialize plan should initialize and get an initial plan
                std::shared_ptr<afrl::cmasi::MissionCommand> ptr_MissionCommand(mission->clone());
                if (isInitializePlan(ptr_MissionCommand))
                {
                    int64_t waypointIdCurrent = {ptr_MissionCommand->getWaypointList().front()->getNumber()};
                    std::cout << "!!!waypointIdCurrent is " << waypointIdCurrent << std::endl;
                    //waypointIdCurrent is 100004001
                    int64_t idMissionSegmentTemp = {-1};
                    isGetCurrentSegment(waypointIdCurrent, _nextMissionCommandToSend, idMissionSegmentTemp);
                }
                break;
            }
        }
    }    
    
     else if (uxas::messages::task::isTaskPlanOptions(messageObject.get()))
    {
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        auto taskOptions = std::static_pointer_cast<uxas::messages::task::TaskPlanOptions>(messageObject);
        std::string VehicleID = "nul";
        std::string msgName = taskOptions->getFullLmcpTypeName();
        std::cout << "taskOptions received" << std::endl;
        myfile << currentTimeStamp << "   " << VehicleID << "   " << msgName << "\n";
    }
    
    else if (uxas::messages::task::isAssignmentCostMatrix(messageObject.get()))
    {
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        auto assignmentCostMatrix = std::static_pointer_cast<uxas::messages::task::AssignmentCostMatrix>(messageObject);
        std::string VehicleID = "nul";
        std::string msgName = assignmentCostMatrix->getFullLmcpTypeName();
        std::cout << "CostMatrix received" << std::endl;
        myfile << currentTimeStamp << "   " << VehicleID << "   " << msgName << "\n";
    }   
    
    else if (receivedLmcpMessage->m_object->getFullLmcpTypeName() == uxas::messages::task::TaskAssignmentSummary::Subscription)
    {
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        auto taskAssignmentSummary = std::static_pointer_cast<uxas::messages::task::TaskAssignmentSummary>(messageObject);
        //auto assignmentCostMatrix = std::static_pointer_cast<uxas::messages::task::AssignmentCostMatrix>(messageObject);
        std::string VehicleID = "nul";
        std::string msgName = taskAssignmentSummary->getFullLmcpTypeName();
        std::cout << "taskAssignmentSummary received" << std::endl;
        myfile << currentTimeStamp << "   " << VehicleID << "   " << msgName << "\n";
    }
    
    else if (uxas::messages::task::isTaskImplementationRequest(messageObject.get())){
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        auto taskImplementationRequest = std::static_pointer_cast<uxas::messages::task::TaskImplementationRequest>(messageObject);
        std::string VehicleID = "nul";
        std::string msgName = taskImplementationRequest->getFullLmcpTypeName();
        std::cout << "taskImplementationRequest received" << std::endl;
        myfile << currentTimeStamp << "   " << VehicleID << "   " << msgName << "\n";
    }
    else if (uxas::messages::task::isTaskImplementationResponse(messageObject.get())){
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        auto taskImplementationResponse = std::static_pointer_cast<uxas::messages::task::TaskImplementationResponse>(messageObject);
        std::string VehicleID = "nul";
        std::string msgName = taskImplementationResponse->getFullLmcpTypeName();
        std::cout << "taskImplementationResponse received" << std::endl;
        myfile << currentTimeStamp << "   " << VehicleID << "   " << msgName << "\n";
    }
    else if (uxas::messages::route::isRoutePlanRequest(messageObject.get())){
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        auto routePlanRequest = std::static_pointer_cast<uxas::messages::route::RoutePlanRequest>(messageObject);
        std::string VehicleID = "nul";
        std::string msgName = routePlanRequest->getFullLmcpTypeName();
        std::cout << "routePlanResponse received" << std::endl;
        myfile << currentTimeStamp << "   " << VehicleID << "   " << msgName << "\n";
    }    
    else if (uxas::messages::route::isRoutePlanResponse(messageObject.get())){
        long currentTimeStamp = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        auto routePlanResponse = std::static_pointer_cast<uxas::messages::route::RoutePlanResponse>(messageObject);
        std::string VehicleID = "nul";
        std::string msgName = routePlanResponse->getFullLmcpTypeName();
        std::cout << "routePlanResponse received" << std::endl;
        myfile << currentTimeStamp << "   " << VehicleID << "   " << msgName << "\n";
    }
    return false;
}

bool BackToBeginAttack::isGetNextWaypointId(const int64_t& waypointIdCurrent, int64_t & waypointIdNext)
{
    bool isSucceeded(false);
    //for each segment
    for (auto itSegment = m_missionSegments.begin(); itSegment != m_missionSegments.end(); itSegment++)
    {
        bool isFoundCurrent = {false};
        //check if current waypoint ID == the waypoint id in this segment
        for (auto itWaypoint = (*itSegment)->getWaypointList().begin(); itWaypoint != (*itSegment)->getWaypointList().end(); itWaypoint++)
        {
            if ((*itWaypoint)->getNumber() == waypointIdCurrent)
            {
                isFoundCurrent = true;
                std::cout << "waypointIdCurrent:" << std::endl;
                std::cout << waypointIdCurrent << std::endl;
            }
            //if the above check is failed, in the next iteration, assign the next id number
            else if (isFoundCurrent)
            {
                waypointIdNext = (*itWaypoint)->getNumber();
                std::cout << "waypointIdNext:" << std::endl;
                std::cout << waypointIdNext << std::endl;               
                isSucceeded = true;
                break;
            }
        }
    }

    return (isSucceeded);
}
//// the second argument "segmentCurrent" is the command
bool BackToBeginAttack::isGetCurrentSegment(const int64_t& waypointIdCurrent, std::shared_ptr<avtas::lmcp::Object>& segmentCurrent, int64_t & idMissionSegmentCurrent)
{
    bool isSucceeded(false);

    // return segment in segmentCurrent. does not change segmentCurrent if a segment is not found or is already current
    // if a pointer is generated, this function gives up ownership on return

    // search through all of the segments and find the last segment with this waypointID
    std::shared_ptr<afrl::cmasi::MissionCommand> segmentTemp;
    
    ////size of m_missionSegments is 8 or 0 
//    for (auto itSegment = m_missionSegments.begin(); itSegment != m_missionSegments.end(); itSegment++)
//    {
//        //search through the waypoint list in the segment
//        for (auto itWaypoint = (*itSegment)->getWaypointList().begin(); itWaypoint != (*itSegment)->getWaypointList().end(); itWaypoint++)
//        {
//            // find a waypoint match the current waypoint id
//            if ((*itWaypoint)->getNumber() == waypointIdCurrent)
//            {
//                // if possible, don't choose a segment where the desired waypoint is first, unless it is the first segment
//                if ((itWaypoint != (*itSegment)->getWaypointList().begin()) || (!segmentTemp)) // not first waypoint in the segment OR (not yet found))
//                {
//                    segmentTemp = *itSegment;
//                    ////int64_t myTemp = segmentTemp->getCommandID();
//                    ////modify the segment to the first segment
//                    ////try dont modify segmentTemp here
//                    ////segmentTemp= *m_missionSegments.begin();
//                    
//                    ////tested, the two vars are the same when UAV is at the middle of a segment
//                    ////std::cout << "!!!segmentTemp id is " << myTemp << std::endl;
//                    ////std::cout << "!!!m_idMissionSegmentCurrent is " << m_idMissionSegmentCurrent << std::endl;
//                }
//                //break;
//            }
//        }
//    }
    
    ////once UAV reaches waypoint in next segment, segmentTemp->getCommandID() will not be the same as m_idMissionSegmentCurrent
    ////once UAV reaches waypoint in next segment, assign new mission command and make it not null, so we can send,
    //// at the same time, we make a fake mission command
    
//    if (segmentTemp && (segmentTemp->getCommandID() != m_idMissionSegmentCurrent))
//    {
        ////try attack here, still work
        ////m_missionSegments.back() and m_missionSegments.front() both go back to the begin point, why?
        
        //segmentTemp= m_missionSegments.front();
        //std::cout << "!!!m_missionSegments size is " << m_missionSegments.size() << std::endl;
        segmentTemp= m_missionSegments.front();
        COUT_INFO("!!! Modified Segment: m_idMissionSegmentNew[" << segmentTemp->getCommandID() << "] m_idMissionSegmentOld[" << m_idMissionSegmentCurrent << "] waypointIdCurrent[" << waypointIdCurrent << "] First Segment Waypoint[" << segmentTemp->getWaypointList().front()->getNumber() << "] Last[" << segmentTemp->getWaypointList().back()->getNumber() << "]")
        ////size here is always 1
        //std::cout << "!!!m_missionSegments size is " << m_missionSegments.size() <<std::endl;
        ////make them identical
        
        m_idMissionSegmentCurrent = segmentTemp->getCommandID();
        afrl::cmasi::MissionCommand* segmentCurrentLocal = {segmentTemp->clone()};
        ////idMissionSegmentCurrent is one argument, originally empty
        idMissionSegmentCurrent = segmentCurrentLocal->getCommandID();

        // don't "goto" the first waypoint in the segment as the first waypoint to go to
        // this is set as the second waypoint in the segment by default
        if (waypointIdCurrent != segmentCurrentLocal->getWaypointList().front()->getNumber())
        {
            //set the first waypoint id for the segment
            //modify the waypoint!!!!
            //segmentCurrentLocal->setFirstWaypoint(waypointIdCurrent);
            segmentCurrentLocal->setFirstWaypoint(segmentCurrentLocal->getWaypointList().front()->getNumber());
            std::cout << "!!!Modified the waypoint!!!" << std::endl;
            std::cout << "!!!Modified segment ID is " <<m_idMissionSegmentCurrent<< std::endl;
            myfile << "*******************************waypoint modified************" << "\n";
        }
        //reset is similar as deleting the content
        ////segmentCurrent will be the member variable "_nextMissionCommandToSend"
        segmentCurrent.reset(segmentCurrentLocal);
        segmentCurrentLocal = nullptr;
        isSucceeded = true;
    //}

    return (isSucceeded);
}

bool BackToBeginAttack::isInitializePlan(std::shared_ptr<afrl::cmasi::MissionCommand> & ptr_MissionCommand)
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
            ////now missionSegment_01 and missionSegment_02 are still empty
            std::shared_ptr<afrl::cmasi::MissionCommand> missionSegment_01(missionCommandTemp->clone());
            missionSegment_01->setCommandID(getUniqueEntitySendMessageId());
            COUT_INFO("missionSegment_01->getCommandID[" << missionSegment_01->getCommandID() << "]")

            std::shared_ptr<afrl::cmasi::MissionCommand> missionSegment_02(missionCommandTemp->clone());
            missionSegment_02->setCommandID(getUniqueEntitySendMessageId());
            COUT_INFO("missionSegment_02->getCommandID[" << missionSegment_01->getCommandID() << "]")
            

            //parameter is  reference, when set itWaypoint, we also set ptr_MissionCommand
            auto itWaypoint = ptr_MissionCommand->getWaypointList().begin();
            for (; itWaypoint != ptr_MissionCommand->getWaypointList().end(); itWaypoint++)
            {
                //check if the size of waypoint list is less than 100000. 
                ////in waterway search example, it is 15
                //push_back put the element to the end of the list and increase the size by 1
                std::cout << "!!!missionSegment_01->getWaypointList().size() is " <<missionSegment_01->getWaypointList().size()<< std::endl;
                ////start editing a customized waypoint list


                ////m_numberWaypointsToServe is set to 15 by config file in waterway example
                if (missionSegment_01->getWaypointList().size() < m_numberWaypointsToServe)
                {
                    missionSegment_01->getWaypointList().push_back((*itWaypoint)->clone());
                    // check for overlap, if 01 list is close to 100000, we use 02 to store the point
                    ////in most cases, 02 is empty
                    if ((m_numberWaypointsToServe - missionSegment_01->getWaypointList().size()) < m_numberWaypointOverlap)
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
                // if the size is larger than 100000,
                else
                {
                    missionSegment_02->getWaypointList().push_back((*itWaypoint)->clone());
                    if (missionSegment_01->getFirstWaypoint() >= 0)
                    {
                        //in the example it is false.
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
                        CERR_FILE_LINE_MSG("ERROR::BackToBeginAttack::isInitializePlan:: first waypoint of segment was not set!!!!")
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
                //it is false in example
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
                CERR_FILE_LINE_MSG("ERROR::BackToBeginAttack::isInitializePlan:: no m_missionSegments constructed from the MissionCommand!!!!")
                isSucceeded = false;
            }
        }
        else
        {
            CERR_FILE_LINE_MSG("ERROR::BackToBeginAttack::isInitializePlan:: no waypoints found in the MissionCommand!!!!")
            isSucceeded = false;
        }
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::BackToBeginAttack::isInitializePlan:: vehicle ID not > 0!!!!")
        isSucceeded = false;
    }
    return (isSucceeded);
};

void BackToBeginAttack::setTurnType(const afrl::cmasi::TurnType::TurnType& turnType, std::shared_ptr<afrl::cmasi::MissionCommand> & ptr_MissionCommand)
{
    for (auto itWaypoint = ptr_MissionCommand->getWaypointList().begin();
            itWaypoint != ptr_MissionCommand->getWaypointList().end();
            itWaypoint++)
    {
        (*itWaypoint)->setTurnType(turnType);
    }
}

void BackToBeginAttack::OnSendNewMissionTimer()
{
    //std::cout << "OnSendNewMissionTimer is triggered" << std::endl;
    //_nextMissionCommandToSend is a currentSegment
    if (_nextMissionCommandToSend)
    {
        std::cout << "!!!Modified mission sent, mission command is not empty" << std::endl;
        std::cout << "!!!Modified segment ID is " <<m_idMissionSegmentCurrent<< std::endl;
        sendSharedLmcpObjectBroadcastMessage(_nextMissionCommandToSend);
         
        _nextMissionCommandToSend.reset();
    }
}


}; //namespace service
}; //namespace uxas

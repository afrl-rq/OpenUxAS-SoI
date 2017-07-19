

// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   DosAttack
 * Author: steve
 *
 * Created on May 8, 2017, 5:55 PM
 *
 * <Service Type="DosAttack" StringToSend="Option_01" SendPeriod_ms="36" />
 * 
 */

// include header for this service
#include "DosAttack.h"

#include "UxAS_TimerManager.h"
// print outs
#include <iostream>     // std::cout, cerr, etc
#include <chrono>

#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>DosAttack:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();

#define STRING_TIME_BETWEEN_DOS_MSG_MS "TimeBetweenDosMsg_ms"
#define COUT_INFO(MESSAGE) std::cout << "<>!!!DosAttack:: " << MESSAGE << std::endl;std::cout.flush();
// namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{

// this entry registers the service in the service creation registry
DosAttack::ServiceBase::CreationRegistrar<DosAttack>
DosAttack::s_registrar(DosAttack::s_registryServiceTypeNames());

// service constructor
DosAttack::DosAttack()
: ServiceBase(DosAttack::s_typeName(), DosAttack::s_directoryName()) { };

// service destructor
DosAttack::~DosAttack() { };


bool DosAttack::configure(const pugi::xml_node& ndComponent)
{

    
    bool isSuccess(true);
        if (!ndComponent.attribute(STRING_TIME_BETWEEN_DOS_MSG_MS).empty())
    {
        _timeBetweenMissionCommandsMin_ms = ndComponent.attribute(STRING_TIME_BETWEEN_DOS_MSG_MS).as_uint();
        //two IDs, 400 and 500 will be printed out respectively
        //for each vehicle, it has its own m_vehicleID, m_numberWaypointsToServe......
        //WaypointPlanManagerSerive will fetch all the vehicle 400 information first and then do vehicle 500
    }
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(afrl::cmasi::VehicleActionCommand::Subscription);

    return (isSuccess);
}

bool
DosAttack::initialize()
{
    bool bSuccess(true);

    // create and start periodic timer, time interval between two command message is 1000ms
    m_sendNewMissionTimerId = uxas::common::TimerManager::getInstance().createTimer(
                                                                                    std::bind(&DosAttack::OnSendNewMissionTimer, this), "DosAttack::OnSendNewMissionTimer");
    uxas::common::TimerManager::getInstance().startPeriodicTimer(m_sendNewMissionTimerId, _timeBetweenMissionCommandsMin_ms, _timeBetweenMissionCommandsMin_ms);

    return (bSuccess);
};

bool DosAttack::start()
{
    // perform any actions required at the time the service starts
    return (true);
};

bool DosAttack::terminate()
{
    // stop timer
    return true;
}

bool DosAttack::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    std::shared_ptr<avtas::lmcp::Object> messageObject = receivedLmcpMessage->m_object;
    
    if(afrl::cmasi::isAirVehicleState(messageObject.get())){
        airVehicleState = messageObject;

    return false;
    }
    if(afrl::cmasi::isVehicleActionCommand(messageObject.get())){
        vehicleActionCommand = messageObject;
    return false;
    }
}
void DosAttack::OnSendNewMissionTimer()
{
    if (airVehicleState)
    {
        sendSharedLmcpObjectBroadcastMessage(airVehicleState);
        //count++;
//        if(count%10000 == 0 ){
//            std::cout << "!!!Count is " << count << std::endl;
//        }
    }
//        if (vehicleActionCommand)
//    {
//        sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);
////        count++;
////        if(count%10000 == 0 ){
////            std::cout << "!!!Count is " << count << std::endl;
////        }
//    }
}

}; //namespace service
}; //namespace uxas

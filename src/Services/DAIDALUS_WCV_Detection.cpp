// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   DAIDALUS_WCV_Detection.cpp
 * Author: SeanR
 *
 *
 *
 * <Service Type="DAIDALUS_WCV_Detection" OptionString="Option_01" OptionInt="36" />
 * 
 */

// include header for this service
#include "DAIDALUS_WCV_Detection.h"
#include "Daidalus.h"
//#include "Position.h"
//#include "Velocity.h"
//#include "Util.h"
//#include "Constants/Convert.h"

//include for KeyValuePair LMCP Message
#include "afrl/cmasi/KeyValuePair.h" //this is an exemplar
#include "afrl/cmasi/AirVehicleState.h"

#include <iostream>     // std::cout, cerr, etc
#include <cmath>    //cmath::cos, sin, etc
#include <string>   //std::to_string etc

// convenience definitions for the option strings
#define STRING_XML_OPTION_STRING "OptionString"
#define STRING_XML_OPTION_INT "OptionInt"

// useful definitions


namespace {
    void makeVelocityXYZ(double u, double v, double w, double Phi, double Theta, double Psi, double& velocityX, double& velocityY, double& velocityZ)
    {
        velocityX = std::cos(Theta)*std::cos(Psi)*u + (std::sin(Phi)*std::sin(Theta)*std::cos(Psi)-std::cos(Phi)*std::sin(Psi))*v + std::sin(Phi)*std::sin(Psi);
        velocityY = std::cos(Theta)*std::sin(Psi)*u + (std::sin(Phi)*std::sin(Theta)*std::sin(Psi)+std::cos(Phi)*std::cos(Psi))*v + (std::cos(Phi)*std::sin(Theta)*std::sin(Psi)-std::sin(Phi)*std::cos(Psi))*w;
        velocityZ = -std::sin(Theta)*u + std::sin(Phi)*std::cos(Theta)*v + std::cos(Phi)*std::cos(Theta)*w;
    }
}

// namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{   

// this entry registers the service in the service creation registry
DAIDALUS_WCV_Detection::ServiceBase::CreationRegistrar<DAIDALUS_WCV_Detection>
DAIDALUS_WCV_Detection::s_registrar(DAIDALUS_WCV_Detection::s_registryServiceTypeNames());

//create a DAIDALUS object

// service constructor
DAIDALUS_WCV_Detection::DAIDALUS_WCV_Detection()
: ServiceBase(DAIDALUS_WCV_Detection::s_typeName(), DAIDALUS_WCV_Detection::s_directoryName()), daa(larcfm::Daidalus()) { };

// service destructor
DAIDALUS_WCV_Detection::~DAIDALUS_WCV_Detection() { };

bool DAIDALUS_WCV_Detection::configure(const pugi::xml_node& ndComponent)
{
    bool isSuccess(true);

    // process options from the XML configuration node:
    if (!ndComponent.attribute("LookAheadTime").empty())
    {
        m_lookahead_time = ndComponent.attribute("LookAheadTime").as_int();
        daa.parameters.setLookaheadTime(m_lookahead_time, "s");
    }
    if (!ndComponent.attribute("LeftTrack").empty())
    {
        m_left_trk = ndComponent.attribute("LeftTrack").as_double();
        daa.parameters.setLeftTrack(m_left_trk, "deg");
    }
    if (!ndComponent.attribute("RightTrack").empty())
    {
        m_right_trk = ndComponent.attribute("RightTrack").as_double();
        daa.parameters.setRightTrack(m_right_trk, "deg");
    }
    if (!ndComponent.attribute("MinGroundSpeed").empty())
    {
        m_min_gs = ndComponent.attribute("MinGroundSpeed").as_double();
        daa.parameters.setMinGroundSpeed(m_min_gs, "m/s");
    }
    if (!ndComponent.attribute("MaxGroundSpeed").empty())
    {
        m_max_gs = ndComponent.attribute("MaxGroundSpeed").as_double();
        daa.parameters.setMaxGroundSpeed(m_max_gs, "m/s");
    }
    // */
    
    // subscribe to messages::
    //addSubscriptionAddress(afrl::cmasi::KeyValuePair::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    std::cout << "Successfully subscribed to AirVehicleState from DAIDALUS_WCV_Detection." << std::endl;


    return (isSuccess);
}

bool DAIDALUS_WCV_Detection::initialize()
{
    // perform any required initialization before the service is started

    
    //std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

bool DAIDALUS_WCV_Detection::start()
{
    // perform any actions required at the time the service starts
    //std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
};

bool DAIDALUS_WCV_Detection::terminate()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

bool DAIDALUS_WCV_Detection::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object))
    {
        //receive message
        auto airVehicleState = std::static_pointer_cast<afrl::cmasi::AirVehicleState> (receivedLmcpMessage->m_object);
        std::cout << "DAIDALUS_WCV_Detection has received an AirVehicleState at " << airVehicleState->getTime() <<" ms--from Entity " << airVehicleState->getID() << std::endl ;
        //handle message
        auto Total_velocity = airVehicleState->getAirspeed();
        auto Total_velocity_calculated =std::sqrt(std::pow(airVehicleState->getU(),2)+std::pow(airVehicleState->getV(),2)+std::pow(airVehicleState->getW(),2));
        if (std::abs(Total_velocity-Total_velocity_calculated)>0.000001)
        {std::cout << "Danger!! Danger !!  Calculated velocity is not equivalent to broadcast velocity" << std::endl;
        std::cout << "Broadcast velocity = " << Total_velocity << " Calculated velocity = " << Total_velocity_calculated << std::endl;}
        std::unordered_map<int64_t, double> detectedViolations;

        
        //add air vehicle message state to the Daidalus Object
        daidalus_package vehicleInfo;
        vehicleInfo.daidalusPosition = larcfm::Position::makeLatLonAlt(airVehicleState->getLocation()->getLatitude(), "deg",  airVehicleState->getLocation()->getLongitude(), "deg", airVehicleState->getLocation()->getAltitude(), "m") ;      
        auto u = airVehicleState->getU();
        auto v = airVehicleState->getV();
        auto w = airVehicleState->getW();
        auto Phi = airVehicleState->getRoll();
        auto Theta = airVehicleState->getPitch();
        auto Psi = airVehicleState->getHeading();
        double velocityX, velocityY, velocityZ;
        makeVelocityXYZ(u, v, w, n_Const::c_Convert::toRadians(Phi), n_Const::c_Convert::toRadians(Theta), n_Const::c_Convert::toRadians(Psi), velocityX, velocityY, velocityZ);
        auto daidalusVelocityZ = -velocityZ;
        auto daidalusVelocityX = velocityY;
        auto daidalusVelocityY = velocityX;
        vehicleInfo.daidalusVelocity = larcfm::Velocity::makeVxyz(daidalusVelocityX,daidalusVelocityY,"m/s",daidalusVelocityZ,"m/s");
        vehicleInfo.daidalusTime = airVehicleState->getTime()/1000.0;
        // DAIDALUS_WCV_Detection::m_entityId is the ID of the ownship
        daidalusVehicleInfo[airVehicleState->getID()] = vehicleInfo;
        if (daidalusVehicleInfo.size()>1 && daidalusVehicleInfo.count(m_entityId)>0)
        { daa.setOwnshipState(std::to_string(m_entityId),daidalusVehicleInfo[m_entityId].daidalusPosition,daidalusVehicleInfo[m_entityId].daidalusVelocity,daidalusVehicleInfo[m_entityId].daidalusTime);
        for (auto it_intruderId = daidalusVehicleInfo.begin(); it_intruderId!=daidalusVehicleInfo.end(); it_intruderId++)
            {
                if (it_intruderId->first!=m_entityId) //add staleness check to this statement or put check on outer most if
                    {
                    daa.addTrafficState(std::to_string(it_intruderId->first),it_intruderId->second.daidalusPosition,it_intruderId->second.daidalusVelocity,it_intruderId->second.daidalusTime);
                //std::cout << "Added Entity " << it_intruderId->first << " as an intruder to Entity " << m_entityId << std::endl;
                    }
            
            }
        //std::cout << "Number of aircraft according to DAIDALUS: " << daa.numberOfAircraft() << std::endl;
        if (daa.numberOfAircraft()>1)
        {
            //detectedViolations.clear();
            for (int intruderIndex = 1; intruderIndex<=daa.numberOfAircraft()-1; intruderIndex++)
            {
                auto timeToViolation = daa.timeToViolation(intruderIndex);
                if (timeToViolation != PINFINITY && timeToViolation != NaN)
                { 
                    detectedViolations[std::stoi(daa.getAircraftState(intruderIndex).getId(),nullptr,10)] = timeToViolation;
                    //std::cout << "Collision with intruder " << daa.getAircraftState(intruderIndex).getId() << " in " << timeToViolation << " seconds" << std::endl;
                }
            }
        }
        }
        
        
      
        // send out response
        //auto keyValuePairOut = std::make_shared<afrl::cmasi::KeyValuePair>();
        //keyValuePairOut->setKey(s_typeName());
        //keyValuePairOut->setValue(std::to_string(m_serviceId));
        //sendSharedLmcpObjectBroadcastMessage(keyValuePairOut);
        std::cout << "Number of aircraft according to DAIDALUS: " << daa.numberOfAircraft() << std::endl;
        if (daa.numberOfAircraft()>1 && !detectedViolations.empty())
        {
            for (auto itViolations = detectedViolations.begin(); itViolations != detectedViolations.end(); itViolations++)
               std::cout << "Entity " << m_entityId << " will violate the well clear volume with Entity " << itViolations->first << " in " << itViolations->second <<" seconds!!" << std::endl;
        }
        else if(daa.numberOfAircraft()>1)
        {
            std::cout << "No violation of well clear volume detected :^)" << std::endl;
        }
        
    }
    return false;
}

} //namespace service
} //namespace uxas

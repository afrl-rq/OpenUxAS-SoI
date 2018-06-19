// ===============================================================================
// Authors: AFRL/RQQA & NASA/NIA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   IcarousCommunicationService.cpp
 * Authors: Paul Coen & Winston Smith
 *
 * Created on June 14, 2018, 3:55 PM
 *
 * <Service Type="IcarousCommunicationService" OptionString="Option_01" OptionInt="36" />
 * 
 * This file allows connectivity with the ICAROUS system
 * (CRoss Application Translator of Operational Unmanned Systems) 
 * ICAROUS allows cooperative mission planning between UxAS and ICAROUS
 * 
 */
 
 /***********************************************************************************************/
 /*IMPORTANT: There are several known security vulnerabilities in this file. The fixes for      */
 /*these may be closed-source. Do not use this code for real applications without modifications!*/
 /***********************************************************************************************/

// include header for this service
#include "IcarousCommunicationService.h"
#include "WaypointPlanManagerService.h"

#include <iostream>

#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AirVehicleStateDescendants.h"

#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/GimbalAngleAction.h"
#include "afrl/cmasi/LoiterAction.h"
#include "uxas/messages/uxnative/IncrementWaypoint.h"

// convenience definitions for the option strings
#define STRING_XML_OPTION_STRING "OptionString"
#define STRING_XML_OPTION_INT "OptionInt"

// namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{

// this entry registers the service in the service creation registry
IcarousCommunicationService::ServiceBase::CreationRegistrar<IcarousCommunicationService>
IcarousCommunicationService::s_registrar(IcarousCommunicationService::s_registryServiceTypeNames());

// service constructor
IcarousCommunicationService::IcarousCommunicationService()
: ServiceBase(IcarousCommunicationService::s_typeName(), IcarousCommunicationService::s_directoryName()) { };

// service destructor
IcarousCommunicationService::~IcarousCommunicationService() { };


bool IcarousCommunicationService::configure(const pugi::xml_node& ndComponent)
{
    bool isSuccess(true);

    // process options from the XML configuration node:
    if (!ndComponent.attribute(STRING_XML_OPTION_STRING).empty())
    {
        m_option01 = ndComponent.attribute(STRING_XML_OPTION_STRING).value();
    }
    if (!ndComponent.attribute(STRING_XML_OPTION_INT).empty())
    {
        m_option02 = ndComponent.attribute(STRING_XML_OPTION_INT).as_int();
    }

    // subscribe to messages::
    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    
    
    return (isSuccess);
}

bool IcarousCommunicationService::initialize()
{
    // perform any required initialization before the service is started
    std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
        
    //Begin manually-created code. Currently, this section creates a socket and allows a single client (currently closed-source) to connect.
    //Each side will essentially print a "Hello World" message saying they connected to the other, and then write another "Hello World 2"
    //message that the other will read and print. This is done simply to prove connectivity from UxAS.
    //
    //Future work: loop reading/writing, send LMCP messages, publish received LMCP messages, and allow UxAS to
    //continue with calculating waypoints before ICAROUS connects
    //Additionally, use UxAS log function calls rather than fprintf's to stderr
    //
    //This code ONLY works on Linux, since it uses Linux function calls    
    
    //Protocol constants for 3-way ICAROUS authentication handshake    
    const char *protocol1 = "ICAROUS-UxAS_LMCP";
    const char *protocol2 = "ok ";
    const char *sharedSecret = "28a4b77b86aa32715e4c271415b28447b8c08d704fd9ffb1258bced7b7167fe0";
    const char *err = "error";
    
    socklen_t server_len;
    struct sockaddr_in server_address;
    int server_sockfd = -2;
    server_sockfd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if(server_sockfd <= 0){
        fprintf(stderr, "Fatal error, socket could not be made!\n");
        return false;
    }
    //Configure server socket so the port isn't held by OS after program termination
    int i = 1;
    if((setsockopt(server_sockfd, SOL_SOCKET, SO_REUSEADDR, &i, sizeof(i))) == -1){
        fprintf(stderr, "Fatal error, socket could not be set up!\n");
        return false;
    }
    //Resolve endianness issues
    server_address.sin_addr.s_addr = htonl(INADDR_ANY);
    server_address.sin_port = htons(PORT);
            
    //Bind server socket as TCP
    server_address.sin_family = AF_INET;
    server_len = sizeof(server_address);
    if((bind(server_sockfd, (struct sockaddr *)&server_address, server_len)) == -1){
        fprintf(stderr, "Fatal error, socket could not be bound!\n");
        return false;
    }

    //Wait for a single connection (ICAROUS)
    listen(server_sockfd, 1);
    fprintf(stdout, "Waiting for ICAROUS connection.\n");
    client_sockfd = accept(server_sockfd, NULL, NULL);
                
    //Perform 3-way handshake with ICAROUS
    if((write(client_sockfd, protocol1, strlen(protocol1))) <= 0){
        fprintf(stderr, "Fatal error, write communication protocol name to ICAROUS failed!\n");
        close(client_sockfd);
        return false;
    }

    int nread;
    char buffer[strlen(sharedSecret) + 1];
    buffer[strlen(sharedSecret)] = '\0';
    if((nread = read(client_sockfd, buffer, strlen(sharedSecret))) <= 0){
        fprintf(stderr, "Fatal error, could not read ICAROUS password!\n");
        close(client_sockfd);
        return false;
    }
    else if(!strcmp(sharedSecret, buffer)){ //!compare==true indicates the strings are the same
        if((write(client_sockfd, protocol2, strlen(protocol2))) <= 0){
          fprintf(stderr, "Fatal error, write confirmation to ICAROUS failed!\n");
          close(client_sockfd);
          return false;
        }
        //ICAROUS has been accepted, begin communication
        fprintf(stdout, "ICAROUS has connected to UxAS!\n");
    }
    else{
        write(client_sockfd, err, strlen(err));
        close(client_sockfd);
        return false;
    }
    
    return true;
}

bool IcarousCommunicationService::start()
{
    // perform any actions required at the time the service starts
    std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    
    return (true);
};

bool IcarousCommunicationService::terminate()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}
    
bool IcarousCommunicationService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    bool isSuccess = 1;
    
    if (afrl::cmasi::isMissionCommand(receivedLmcpMessage->m_object))
    {
        auto ptr_MissionCommand = std::shared_ptr<afrl::cmasi::MissionCommand>((afrl::cmasi::MissionCommand*)receivedLmcpMessage->m_object->clone());
        auto vehicleID = ptr_MissionCommand->getVehicleID();
        std::cout << "Vehicle ID is " << vehicleID << "\n";
        //TODO:: initialize plan should intialize and get an std::string(n_Const::c_Constant_Strings::strGetPrepend_lmcp() + ":UXNATIVE:IncrementWaypoint")intial plan
        if (true)//isInitializePlan(ptr_MissionCommand))
        {
            //TODO: send received waypoint list to ICAROUS, probably as a byte stream
            std::string messageToSend = ptr_MissionCommand->toString();
            char buffer[20];
            buffer[19] = '\0';
            buffer[0] = 'e';
            while(strcmp(buffer, "acknowledged"))
            {
                write(client_sockfd, "TEST_STRING_UXAS_TEST", strlen("TEST_STRING_UXAS_TEST"));
                int nread = read(client_sockfd, buffer, strlen("acknowledged"));
                buffer[nread] = '\0';
                fprintf(stdout, "%s\n", buffer);
                if(!strcmp(buffer, "stop"))
                {
                    fprintf(stderr, "ICAROUS sent error!");
                    return false;
                }
            }
            fprintf(stdout, "Acknowledged by ICAROUS!\n");
        }
    }
    
    return isSuccess;
}

/*
bool IcarousCommunicationService::isInitializePlan(std::shared_ptr<afrl::cmasi::MissionCommand> & ptr_MissionCommand)
{
    bool isSucceeded(true);
    int m_vehicleID = ptr_MissionCommand->getVehicleID();
    
    if (m_vehicleID > 0)
    {
        m_lastReportedToWaypoint = -1;

        /******* build a new container of mission segments*******
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
}*/

}; //namespace service
}; //namespace uxas

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
    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    
    
    return (isSuccess);
}

bool IcarousCommunicationService::initialize()
{
    // perform any required initialization before the service is started
    std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
        
    //Begin manually-created code. Currently, this section creates a socket and allows several instances of a modified ICAROUS to connect.
    //
    //Future work: translate received messages to LMCP, publish translated LMCP messages
    //Additionally, use UxAS log function calls rather than fprintf's to stderr
    //
    //This code ONLY works on Linux, since it uses Linux function calls  
    
    //Initialize has_gotten_waypoints[]
    for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
    {
        has_gotten_waypoints[i] = false;
    }  
    
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
    listen(server_sockfd, ICAROUS_CONNECTIONS);
    fprintf(stdout, "Waiting for ICAROUS connection.\n");

    for(int connectionNum = 0; connectionNum < ICAROUS_CONNECTIONS; connectionNum++){    
        client_sockfd[connectionNum] = accept(server_sockfd, NULL, NULL);

        //Perform 3-way handshake with ICAROUS
        if((write(client_sockfd[connectionNum], protocol1, strlen(protocol1))) <= 0){
            fprintf(stderr, "Fatal error, write communication protocol name to ICAROUS failed!\n");
            close(client_sockfd[connectionNum]);
            return false;
        }

        int nread;
        char buffer[strlen(sharedSecret) + 1];
        buffer[strlen(sharedSecret)] = '\0';
        if((nread = read(client_sockfd[connectionNum], buffer, strlen(sharedSecret))) <= 0){
            fprintf(stderr, "Fatal error, could not read ICAROUS password!\n");
            close(client_sockfd[connectionNum]);
            return false;
        }
        else if(!strcmp(sharedSecret, buffer)){ //!compare==true indicates the strings are the same
            if((write(client_sockfd[connectionNum], protocol2, strlen(protocol2))) <= 0){
              fprintf(stderr, "Fatal error, write confirmation to ICAROUS failed!\n");
              close(client_sockfd[connectionNum]);
              return false;
            }
            //ICAROUS has been accepted, begin communication
            fprintf(stdout, "ICAROUS has connected to UxAS!\n");
            for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
            {
                icarous_sockets[i] = fdopen(client_sockfd[i], "w");
                if(icarous_sockets[i] == NULL)
                {
                    fprintf(stderr, "Test error\n");
                }
            }
        }
        else{
            write(client_sockfd[connectionNum], err, strlen(err));
            close(client_sockfd[connectionNum]);
            return false;
        }
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
    if (afrl::cmasi::isMissionCommand(receivedLmcpMessage->m_object))
    {
        auto ptr_MissionCommand = std::shared_ptr<afrl::cmasi::MissionCommand>((afrl::cmasi::MissionCommand*)receivedLmcpMessage->m_object->clone());
        auto vehicleID = ptr_MissionCommand->getVehicleID();
        std::cout << "Vehicle ID is " << vehicleID << "\n";
        if (!has_gotten_waypoints[vehicleID - 1])
        {
            has_gotten_waypoints[vehicleID - 1] = true;
            std::string messageToSend = ptr_MissionCommand->toXML();
            fprintf(stdout, "Sending Waypoints to ICAROUS instance %i\n", vehicleID);
            fprintf(icarous_sockets[vehicleID-1], "%s\n", messageToSend.c_str());
        }
    }
    else if(afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
    {
        fprintf(stdout, "In\n");
        auto ptr_Zone = std::shared_ptr<afrl::cmasi::KeepInZone>((afrl::cmasi::KeepInZone*)receivedLmcpMessage->m_object->clone());
        std::string messageToSend = ptr_Zone->toXML();
        for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
        {
            fprintf(icarous_sockets[i], "%s\n", messageToSend.c_str());
        }
    }
    else if(afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
    {
        fprintf(stdout, "Out\n");
        auto ptr_Zone = std::shared_ptr<afrl::cmasi::KeepOutZone>((afrl::cmasi::KeepOutZone*)receivedLmcpMessage->m_object->clone());
        std::string messageToSend = ptr_Zone->toXML();
        for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
        {
            fprintf(icarous_sockets[i], "%s\n", messageToSend.c_str());
        }
    }
    else if(afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object))
    {
        auto ptr_AirVehicleState = std::shared_ptr<afrl::cmasi::AirVehicleState>((afrl::cmasi::AirVehicleState*)receivedLmcpMessage->m_object->clone());
        int vehicleID = ptr_AirVehicleState->getID();
        std::string messageToSend = ptr_AirVehicleState->toXML();
        fprintf(icarous_sockets[vehicleID-1], "%s\n", messageToSend.c_str());
    }
    
    return false;
}

}; //namespace service
}; //namespace uxas

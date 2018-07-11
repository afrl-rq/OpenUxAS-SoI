// ===============================================================================
// Authors: AFRL/RQQA & NASA/NIA
// Organizations: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//                National Aeronautics and Space Administration, National Institute of Aerospace
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
 *
 *  Things still to do:
 *   TODO - translate messages from ICAROUS into LMCP (publish recieved messages)
 *   TODO - Use UxAS logging function and UxAS print statements
 *   
 *   TODO configure - Use options given from the XML
 *   TODO configure - Add error checking to the XML options and subscriptions?
 *
 *   TODO processReceivedLmcpMessage - Condense messages being sent for zones with the newest ICAROUS refactor
 *   TODO processReceivedLmcpMessage - fix hardcoding the number of sats (is there a way to get this???)
 *   TODO processReceivedLmcpMessage - Find if there is a place to get relative altitude from AMASE for the UAVs position
 *   TODO processReceivedLmcpMessage - Locate a place where horizonal accuracy is defined (hdop)
 *   TODO processReceivedLmcpMessage - Locate a place where vertical accuracy is defined (vdop)
 *   TODO processReceivedLmcpMessage - Find a way to get the yaw from AMASE for a given UAV (not default included in the message)
 *   
 *   TODO scan for waypoint reached from AirVehicleState
 *
 *  Notes:
 *   This code ONLY works on Linux, since it uses Linux function calls  
 *   
 *   *************************************************************************************************
 *   * IMPORTANT: There are several known security vulnerabilities in this file. The fixes for these *
 *   * may be closed-source. Do not use this code for real applications without modifications!       *
 *   *************************************************************************************************
 */


// Include header for this service
#include "IcarousCommunicationService.h"
#include "WaypointPlanManagerService.h"

#include <iostream>

#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AirVehicleStateDescendants.h"
#include "afrl/cmasi/Polygon.h"
#include "afrl/cmasi/AbstractGeometry.h"


#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/GimbalAngleAction.h"
#include "afrl/cmasi/LoiterAction.h"
#include "afrl/cmasi/FlightDirectorAction.h"
#include "uxas/messages/uxnative/IncrementWaypoint.h"


// Convenience definitions for the option strings
#define STRING_XML_OPTION_STRING "OptionString"
#define STRING_XML_OPTION_INT "OptionInt"

// Namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{



// This entry registers the service in the service creation registry
IcarousCommunicationService::ServiceBase::CreationRegistrar<IcarousCommunicationService>
IcarousCommunicationService::s_registrar(IcarousCommunicationService::s_registryServiceTypeNames());



// Service constructor
IcarousCommunicationService::IcarousCommunicationService()
: ServiceBase(IcarousCommunicationService::s_typeName(), IcarousCommunicationService::s_directoryName()) { };



// Service destructor
IcarousCommunicationService::~IcarousCommunicationService() { };



// Add subscriptions to other services & grab the xml configurations set for the mission
bool IcarousCommunicationService::configure(const pugi::xml_node& ndComponent)
{
    bool isSuccess(true);

// <Service Type="IcarousCommunicationService" NumberOfUAVs="2" />

    // option 2 (TODO - actually use and error check)
    if (!ndComponent.attribute(STRING_XML_ICAROUS_CONNECTIONS).empty())
    {
        ICAROUS_CONNECTIONS = ndComponent.attribute(STRING_XML_ICAROUS_CONNECTIONS).as_int();
    }
    else
    {
        fprintf(stderr, "Number of UAVs not specified!\nTry to use a string such as:\t<Service Type=\"IcarousCommunicationService\" NumberOfUAVs=\"2\" /> in the XML.\n");
        isSuccess = false;
    }


    // Subscribe to messages::
    // MissionCommand messages are used to determine where a singular UAV is going to go during a mission
    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    
    // KeepInZone messages are used to define all zones to stay within
    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    
    // KeepOutZone messages are used to define all zones to stay out of
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    
    // AirVehicleStates are returned from OpenAMASE to know where a UAV is and what it is doing
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);

    // Other message subscriptions should go here


    // Alway true, configuration should not fail (TODO - do not assume success, check for failure with XML options?)
    return (isSuccess);
}



// Start up the module and connect to ICAROUS instance(s)
bool IcarousCommunicationService::initialize()
{
    // Perform any required initialization before the service is started
    std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;


    //Set both vectors to the Number of UAVs specified in the XML
    client_sockfd.resize(ICAROUS_CONNECTIONS);
    has_gotten_waypoints.resize(ICAROUS_CONNECTIONS);
    
    // Initialize has_gotten_waypoints[] to the number of UAVs that is planned on being used
    has_gotten_waypoints.assign(ICAROUS_CONNECTIONS,false);    
    
    
    // Variable set-up
    // Protocol constants for 3-way ICAROUS authentication handshake    
    const char *protocol1 = "ICAROUS-UxAS_LMCP";
    const char *protocol2 = "ok ";
    const char *sharedSecret = "28a4b77b86aa32715e4c271415b28447b8c08d704fd9ffb1258bced7b7167fe0";
    const char *err = "error";
    
    // Other variables
    int server_sockfd = -2;
    int i = 1;
    int nread;
    int nwrite;
    char buffer[strlen(sharedSecret) + 1];
        
    // Set up an IPv4 socket & make it stream-based and close on exec
    socklen_t server_len;
    struct sockaddr_in server_address;
    server_sockfd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    
    // Check to make sure that the socket was created
    if(server_sockfd <= 0)
    {
        fprintf(stderr, "Fatal error, socket could not be made!\n");
        return false;
    }
    
    // Configure server socket so the port isn't held by OS after program termination
    if((setsockopt(server_sockfd, SOL_SOCKET, SO_REUSEADDR, &i, sizeof(i))) == -1)
    {
        fprintf(stderr, "Fatal error, socket could not be set up!\n");
        return false;
    }
    
    // Resolve endianness issues
    server_address.sin_addr.s_addr = htonl(INADDR_ANY);
    server_address.sin_port = htons(PORT);

    // Bind server socket as TCP (IPv4)
    server_address.sin_family = AF_INET;
    server_len = sizeof(server_address);
    if((bind(server_sockfd, (struct sockaddr *)&server_address, server_len)) == -1)
    {
        fprintf(stderr, "Fatal error, socket could not be bound!\n");
        return false;
    }

    // Wait for a single connection (ICAROUS)
    listen(server_sockfd, ICAROUS_CONNECTIONS);
    fprintf(stdout, "Waiting for ICAROUS connection.\n");

    // Once the first has initiated the first step of connecting, accept the number of ICAROUS' defined by the mission
    for(int connectionNum = 0; connectionNum < ICAROUS_CONNECTIONS; connectionNum++)
    {    
        // Accept another new ICAROUS connection
        client_sockfd[connectionNum] = accept(server_sockfd, NULL, NULL);

        // Perform 3-way handshake with ICAROUS
        // Start with the protocol that is expected
        if((write(client_sockfd[connectionNum], protocol1, strlen(protocol1))) <= 0)
        {
            fprintf(stderr, "Fatal error, write communication protocol name to ICAROUS failed!\n");
            close(client_sockfd[connectionNum]);
            return false;
        }

        // Reset the variables from the last itteration
        nread = 0;
        buffer[strlen(sharedSecret)] = '\0';
        
        // Read for the password from ICAROUS
        if((nread = read(client_sockfd[connectionNum], buffer, strlen(sharedSecret))) <= 0)
        {
            // Password reading was interupted
            
            fprintf(stderr, "Fatal error, could not read ICAROUS password!\n");
            close(client_sockfd[connectionNum]);
            return false;
        }
        else if(!strcmp(sharedSecret, buffer)) // !compare==true indicates the strings are the same
        {
            // Password was acepted and recognized
            
            // Respond back to ICAROUS instance to inform it of the connection status
            if((write(client_sockfd[connectionNum], protocol2, strlen(protocol2))) <= 0){
              fprintf(stderr, "Fatal error, write confirmation to ICAROUS failed!\n");
              close(client_sockfd[connectionNum]);
              return false;
            }
            
            // ICAROUS has been accepted, begin communication
            fprintf(stdout, "ICAROUS[%i] has connected to UxAS!\n", client_sockfd[connectionNum]);
        }
        else
        {
            // Password was incorrect or another error was encountered
            
            nwrite = write(client_sockfd[connectionNum], err, strlen(err));
            fprintf(stderr, "Able to write %i bytes to ICAROUS reporting an error.\n", nwrite);
            close(client_sockfd[connectionNum]);
            return false;
        }
    }
    
    // Initialization was successful
    return true;
}



// This function is used to start the service
bool IcarousCommunicationService::start()
{
    // perform any actions required at the time the service starts
    std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;

    // Start children here to begin reading from ICAROUS instances
    for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
    {
        fprintf(stdout, "Creating a child to read from ICAROUS; Child #%i\n", (i+1));
        if((readIcarousID = fork()) == 0){
            ICAROUS_listener(client_sockfd[i]);
            
            // If the child gets here, there was a major error
            fprintf(stderr, "Error with a child reading from ICAROUS!\n");
            terminate();
        }
        else if(readIcarousID == -1)
        {
            fprintf(stderr, "Error with creating a child to read from ICAROUS!\n");
            terminate();
        }
    }
    
    return (true);
};


// Listener for ICAROUS command messages
bool IcarousCommunicationService::ICAROUS_listener(int64_t icarousClientFd)
{
    fprintf(stdout, "Child created for icarousClientFd: %lli\n", icarousClientFd);
    
    const int max_message_length = 87040;
    char messageBuffer[max_message_length + 1];
    
    // Listen to ICAROUS forever
    while(true){
        fprintf(stdout, "Child listening to icarousClientFd: %lli\n", icarousClientFd);        
        
        messageBuffer[0] = '\0';
        int nread = max_message_length;
        int bytesReceived = 0;
        errno = 0;
        
        //listen to each client socket
        //Read any messages ICAROUS has posted
        
        while(nread == max_message_length && !errno){
            fprintf(stdout, "Read call made in icarousClientFd %lli\n", icarousClientFd);
            nread = read(icarousClientFd, messageBuffer, max_message_length);
            bytesReceived += nread;
        }
        
        messageBuffer[bytesReceived] = '\0'; //makes sure we never segfault
        
        //fprintf(stdout, "Full message from child socket #%lli:\n%s\n", icarousClientFd, messageBuffer);
        
        char *tempMessageBuffer = messageBuffer;
        
        while(strlen(tempMessageBuffer)){
        
            // Necessary variables
            char *fieldEnd;
            char throwaway[400]; // Used simply to fill necessary (but useless) arguments in function calls
            int fieldLength;
            char *trackingHelper;
            
            if(!strncmp(tempMessageBuffer, "SETMOD", 6)) // Set Mode (has ICAROUS taken over?)
            {
                // SETMOD,type~,\n
                fprintf(stdout, "icarousClientFd %lli|SETMOD message received!\n", icarousClientFd);
                
                // The following section of code finds several fields by their tags.
                // It's fairly difficult to follow, so here's a comment section explaining each line.            
                /* 1. strstr returns a pointer to the first occurence of our tag in the message
                 * 2. Use pointer arithmetic to skip past the tag
                 * 3. Find the end of the field (they're variable length) using the ',' delimiter
                 * 4. Get the length of the field via pointer arithmetic (end - beginning)
                 * 5. Convert the field to a usable number and store it into the message to be published to cFS
                 */
                // Note: We tried to functionize this code. We spent 4 hours and had the strangest
                // issue we've ever seen, with a passed-in pointer being invalid memory to access.
                // Possible it was a unique issue.
                
                // Mode type
                trackingHelper            = strstr(tempMessageBuffer, "type");
                trackingHelper           += 4; // skip past "type"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                int modeType     = atof(strncpy(throwaway, trackingHelper, fieldLength));


                fprintf(stdout, "%lli|SETMOD|modeType|%i\n", icarousClientFd, modeType);

                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else if(!strncmp(tempMessageBuffer, "SETPOS", 6))
            {
                // SETPOS,lat~,long~,alt~,\n
                fprintf(stdout, "SETPOS message received in icarousClientFd %lli!\n", icarousClientFd);
                
                // Get latitude
                trackingHelper            = strstr(tempMessageBuffer, "lat");
                trackingHelper           += 3; //skip past "lat"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float latitude     = atof(strncpy(throwaway, trackingHelper, fieldLength));

                // Get longitude
                trackingHelper            = strstr(tempMessageBuffer, "long");
                trackingHelper           += 4; //skip past "long"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float longitude     = atof(strncpy(throwaway, trackingHelper, fieldLength));

                // Get altitude
                trackingHelper            = strstr(tempMessageBuffer, "alt");
                trackingHelper           += 3; //skip past "alt"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float altitude     = atof(strncpy(throwaway, trackingHelper, fieldLength));


                fprintf(stdout, "%lli|SETMOD|latitude|%f\n", icarousClientFd, latitude);
                fprintf(stdout, "%lli|SETMOD|longitude|%f\n", icarousClientFd, longitude);
                fprintf(stdout, "%lli|SETMOD|altitude|%f\n", icarousClientFd, altitude);
                

                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else if(!strncmp(tempMessageBuffer, "SETVEL", 6))
            {
                // SETVEL,u~,v~,w~,\n
                fprintf(stdout, "SETVEL message received in icarousClientFd %lli!\n", icarousClientFd);
                
                // Get u
                trackingHelper            = strstr(tempMessageBuffer, "u");
                trackingHelper           += 1; //skip past "u"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float u     = atof(strncpy(throwaway, trackingHelper, fieldLength));

                // Get v
                trackingHelper            = strstr(tempMessageBuffer, "v");
                trackingHelper           += 1; //skip past "v"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float v     = atof(strncpy(throwaway, trackingHelper, fieldLength));

                // Get w
                trackingHelper            = strstr(tempMessageBuffer, "w");
                trackingHelper           += 1; //skip past "w"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float w     = atof(strncpy(throwaway, trackingHelper, fieldLength));

                
                fprintf(stdout, "%lli|SETVEL|u|%f\n", icarousClientFd, u);
                fprintf(stdout, "%lli|SETVEL|v|%f\n", icarousClientFd, v);
                fprintf(stdout, "%lli|SETVEL|w|%f\n", icarousClientFd, w);
                
                
                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else if(!strncmp(tempMessageBuffer, "GOTOWP", 6))
            {
                // GOTOWP,id~,\n
                fprintf(stdout, "GOTOWP message received in icarousClientFd!\n", icarousClientFd);
                
                // Get id
                trackingHelper            = strstr(tempMessageBuffer, "id");
                trackingHelper           += 2; //skip past "id"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                int id     = atof(strncpy(throwaway, trackingHelper, fieldLength));
                
                
                fprintf(stdout, "%lli|GOTOWP|id|%i\n", icarousClientFd, id);
                
                
                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }            
            else
            {
                //fprintf(stderr,"Error, unknown message type!\n");
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
                //exit(EXIT_FAILURE);
            }
        }
        
        
    }
}


// This function is performed to cleanly terminate the service
bool IcarousCommunicationService::terminate()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}



// Listen for defined messages and relay them to the needed ICAROUS instance they belong to
bool IcarousCommunicationService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    // Process a MissionCommand message
    if (afrl::cmasi::isMissionCommand(receivedLmcpMessage->m_object))
    {
        // Copy the message pointer to shorten access length
        auto ptr_MissionCommand = std::shared_ptr<afrl::cmasi::MissionCommand>((afrl::cmasi::MissionCommand*)receivedLmcpMessage->m_object->clone());
        
        // Grab the vehicles's ID to use as an index + 1
        auto vehicleID = ptr_MissionCommand->getVehicleID();
        std::cout << "Vehicle ID is " << vehicleID << "\n";
        
        // Check that the vehicle has not already recieved its waypoints
        if (!has_gotten_waypoints[vehicleID - 1])
        {
            // Set the variable to ensure we only send one vehicle one MissionCommand
            has_gotten_waypoints[vehicleID - 1] = true;
            fprintf(stdout, "Sending waypoints to ICAROUS instance %lld\n", vehicleID);

            // Set up variable to be used
            int waypointIndex = (ptr_MissionCommand->getFirstWaypoint() - 1);
            int totalNumberOfWaypoints = (ptr_MissionCommand->getWaypointList().size() - 1);
            int nextWaypoint = ptr_MissionCommand->getWaypointList()[waypointIndex]->getNextWaypoint();

            // For each waypoint in the mission command, send each as its own message to ICAROUS
            // The last waypoint's next value will be equal to itself (This indicates the end)
            while(nextWaypoint != ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber())
            {
                //fprintf(stdout, "WaypointIndex: %i | nextWaypoint: %i\n", waypointIndex, nextWaypoint);
                //fprintf(stdout, "Sending Waypoint: %i\n", ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber());
                //fprintf(stdout, "Sending a waypoint to ICAROUS[%i]\n", client_sockfd[vehicleID-1]);

                // Actually set up the message to send using dprintf and send along the socket
                dprintf(client_sockfd[vehicleID - 1], "WAYPT,total%i.0,speed%f,lat%f,long%f,alt%f,index%lld.0,\n",
                    totalNumberOfWaypoints,
                    ptr_MissionCommand->getWaypointList()[waypointIndex]->getSpeed(),
                    ptr_MissionCommand->getWaypointList()[waypointIndex]->getLatitude(), 
                    ptr_MissionCommand->getWaypointList()[waypointIndex]->getLongitude(), 
                    ptr_MissionCommand->getWaypointList()[waypointIndex]->getAltitude(),
                    (ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber() - 1));

                // Set the index of the next waypoint
                waypointIndex = (nextWaypoint - 1);
                
                // Grab the next waypoint's next waypoint to check if it is the end
                nextWaypoint = ptr_MissionCommand->getWaypointList()[waypointIndex]->getNextWaypoint();
            }
            
            //Send a message to ICAROUS telling it to start the mission
            dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,\n",
            "START_MISSION");
        }
    }// End of MissionCommand
    // Process a KeepInZone
    else if(afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
    {
        fprintf(stdout, "Keep In Geofence\n");
        
        // Copy the message pointer to shorten access length
        auto ptr_Zone = std::shared_ptr<afrl::cmasi::KeepInZone>((afrl::cmasi::KeepInZone*)receivedLmcpMessage->m_object->clone());
        
        // Get the number of vertices of the polygon zone
        int lengthOfZone = ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints().size();
        fprintf(stdout, "Length of KeepIn:%i\n", lengthOfZone);


        // Broadcast this message to all ICAROUS instances
        for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
        {
            // Send each zone's vertices one at a time
            // TODO - Condense this with the newest ICAROUS refactor
            for(int j = 0; j < lengthOfZone; j++)
            {
                dprintf(client_sockfd[i], "GEOFN,type%s,totalvert%i.0,vertIndex%i,lat%f,long%f,floor%f,ceil%f,index%lli.0,\n",
                    "_KEEPIN_",
                    lengthOfZone,
                    (j + 1),
                    ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints()[j]->getLatitude(),
                    ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints()[j]->getLongitude(),
                    ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints()[j]->getAltitude(),
                    100000.0,
                    ptr_Zone->getZoneID());
            }
            
            //Send a message to ICAROUS telling it to start the mission
            dprintf(client_sockfd[i], "COMND,type%s,\n",
            "GEOFN_SEND");
        }
    }// End of KeepInZone
    // Process a KeepOutZone
    else if(afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
    {
        fprintf(stdout, "Keep Out Geofence\n");
        
        // Copy the message pointer to shorten access length
        auto ptr_Zone = std::shared_ptr<afrl::cmasi::KeepOutZone>((afrl::cmasi::KeepOutZone*)receivedLmcpMessage->m_object->clone());
        
        // Get the number of vertices of the polygon zone
        int lengthOfZone = ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints().size();
        fprintf(stdout, "Length of KeepOut:%i\n", lengthOfZone);


        // Broadcast this message to all ICAROUS instances
        for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
        {
            // Send each zone's vertices one at a time
            // TODO - Condense this with the newest ICAROUS refactor
            for(int j = 0; j < lengthOfZone; j++)
            {
                dprintf(client_sockfd[i], "GEOFN,type%s,totalvert%i.0,vertIndex%i.0,lat%f,long%f,floor%f,ceil%f,index%lld.0,\n",
                    "_KEEPOUT_",
                    lengthOfZone,
                    (j + 1),
                    ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints()[j]->getLatitude(),
                    ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints()[j]->getLongitude(),
                    ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints()[j]->getAltitude(),
                    100000.0,
                    ptr_Zone->getZoneID());
            }
            
            //Send a message to ICAROUS telling it to start the mission
            dprintf(client_sockfd[i], "COMND,type%s,\n",
            "GEOFN_SEND");
        }
    }// End of KeepOutZone Check
    // Process an AirVehicleState from OpenAMASE
    else if(afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object))
    {
        // Copy the message pointer to shorten access length
        auto ptr_AirVehicleState = std::shared_ptr<afrl::cmasi::AirVehicleState>((afrl::cmasi::AirVehicleState *)receivedLmcpMessage->m_object->clone());
        int vehicleID = ptr_AirVehicleState->getID();

        // Send the position of the UAV to ICAROUS every time it updates from AMASE
        // TODO - un-hardcode the number of sats
        dprintf(client_sockfd[vehicleID - 1], "POSTN,timegps%f,lat%f,long%f,altabs%f,altrel%f,vx%f,vy%f,vz%f,hdop%f,vdop%f,numsats%i.0,id%i.0,\n",
            ((double)ptr_AirVehicleState->getTime()/1000),
            ptr_AirVehicleState->getLocation()->getLatitude(),
            ptr_AirVehicleState->getLocation()->getLongitude(),
            ptr_AirVehicleState->getLocation()->getAltitude(),
            ptr_AirVehicleState->getLocation()->getAltitude(),// TODO - come back to this, rel altitude != abs altitude
            ptr_AirVehicleState->getU(),
            ptr_AirVehicleState->getV(),
            ptr_AirVehicleState->getW(),
            0.1,// TODO - actual horizontal accuracy
            0.1,// TODO - actual vertical accuracy
            25,
            vehicleID);

        /*
        dprintf(1, "POSTN,timegps%f,lat%f,long%f,altabs%f,altrel%f,vx%f,vy%f,vz%f,hdop%f,vdop%f,numsats%i.0,id%i.0,\n",
            ((double)ptr_AirVehicleState->getTime()/1000),
            ptr_AirVehicleState->getLocation()->getLatitude(),
            ptr_AirVehicleState->getLocation()->getLongitude(),
            ptr_AirVehicleState->getLocation()->getAltitude(),
            ptr_AirVehicleState->getLocation()->getAltitude(),// TODO - come back to this, rel altitude != abs altitude
            ptr_AirVehicleState->getU(),
            ptr_AirVehicleState->getV(),
            ptr_AirVehicleState->getW(),
            0.1,// TODO - actual horizontal accuracy
            0.1,// TODO - actual vertical accuracy
            25,
            vehicleID);
        */

        // Send the attitude of the UAV (roll,pitch,yaw) every time it updates from AMASE
        dprintf(client_sockfd[vehicleID - 1], "ATTUD,roll%f,pitch%f,yaw%f,\n",
            ptr_AirVehicleState->getRoll(),
            ptr_AirVehicleState->getPitch(),
            0.0);// TODO - find a way to actually get Yaw (no way currently from AirVehicleState)


        // For all other ICAROUS connections, send the UAV as a traffic obsticle to avoid
        for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
        {
            if(i != (vehicleID - 1))
            {
                // Send the UAV obsticle along the socket as other air traffic
                dprintf(client_sockfd[i], "OBJCT,type%s,lat%f,long%f,alt%f,vx%f,vy%f,vz%f,index%i.0,\n",
                    "_TRAFFIC_",//either _TRAFFIC_ or _OBSTACLE_
                    ptr_AirVehicleState->getLocation()->getLatitude(),
                    ptr_AirVehicleState->getLocation()->getLongitude(),
                    ptr_AirVehicleState->getLocation()->getAltitude(),
                    ptr_AirVehicleState->getU(),
                    ptr_AirVehicleState->getV(),
                    ptr_AirVehicleState->getW(),
                    vehicleID); // ICAROUS indexes start at 1 normally
            }
        }

        // TODO scan for waypoint reached from AirVehicleState
        // Order does not matter as long as we save the list and use the indexing
        // 1.) Save the MissionCommand for each UAV
        // 2.) When the current waypoint changes, send the older one as completed

    }// End of AirVehicleState


    // False indicates that we are ready to process more messages
    return false;
}

}; //namespace service
}; //namespace uxas

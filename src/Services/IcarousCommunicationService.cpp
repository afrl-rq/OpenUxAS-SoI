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
#include "afrl/cmasi/CommandStatusType.h"
#include "afrl/cmasi/FlightDirectorAction.h"
#include "afrl/cmasi/GimbalAngleAction.h"
#include "afrl/cmasi/GoToWaypointAction.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/LoiterAction.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/NavigationMode.h"
#include "afrl/cmasi/VehicleActionCommand.h"

#include "uxas/messages/uxnative/IncrementWaypoint.h"
#include "uxas/messages/task/TaskPause.h"
#include "uxas/messages/task/TaskResume.h"


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
    // TODO - semaphores are system-wide, since they're implemented as files. Lock a semaphore in this thread when
    // we don't want to re-run UxAS, and unlock it when we do. Additionally, in the terminate function for this service,
    // delete the semaphore file.
    // TODO TODO - Instead of going through all that, try setting the troublesome service to only send its troublesome
    // message once, ever
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


    // Set both vectors to the Number of UAVs specified in the XML
    client_sockfd.resize(ICAROUS_CONNECTIONS);
    has_gotten_waypoints.resize(ICAROUS_CONNECTIONS);
    icarousClientWaypointLists.resize(ICAROUS_CONNECTIONS);
    entityTasks.resize(ICAROUS_CONNECTIONS);
    icarousTakeoverActive.resize(ICAROUS_CONNECTIONS);
    currentInformation.resize(ICAROUS_CONNECTIONS);
    positionBeforeTakeover.resize(ICAROUS_CONNECTIONS);
    icarousID.resize(ICAROUS_CONNECTIONS);
    currentWaypointIndex.resize(ICAROUS_CONNECTIONS);
    lastWaypoint.resize(ICAROUS_CONNECTIONS);
    isLastWaypointInitialized.resize(ICAROUS_CONNECTIONS);
    missionCommands.resize(ICAROUS_CONNECTIONS);
    newWaypointLists.resize(ICAROUS_CONNECTIONS);
    softResetFlag.resize(ICAROUS_CONNECTIONS);
    resumePointSet.resize(ICAROUS_CONNECTIONS);
    truncateWaypoint.resize(ICAROUS_CONNECTIONS);
    
    // Mutexes must be set like this and not in a vector
    // This is because a vector of mutexes is non-resizable
    currentInformationMutexes = new std::mutex[ICAROUS_CONNECTIONS];
    
    softResetSemaphores = new sem_t[ICAROUS_CONNECTIONS];
    
    for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
    {
        currentInformation[i].resize(4); // This is to set the size of heading, lat, long, and alt for each instance
        positionBeforeTakeover[i].resize(4);
        sem_init(&softResetSemaphores[i], 0, 0);
    }

    // Initialize has_gotten_waypoints[] to the number of UAVs that is planned on being used
    has_gotten_waypoints.assign(ICAROUS_CONNECTIONS,false);    
    icarousTakeoverActive.assign(ICAROUS_CONNECTIONS, false);
    currentWaypointIndex.assign(ICAROUS_CONNECTIONS, 0);
    lastWaypoint.assign(ICAROUS_CONNECTIONS, -1);
    isLastWaypointInitialized.assign(ICAROUS_CONNECTIONS, false);
    softResetFlag.assign(ICAROUS_CONNECTIONS, false);
    resumePointSet.assign(ICAROUS_CONNECTIONS, false);
    truncateWaypoint.assign(ICAROUS_CONNECTIONS, false);
    
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
        fprintf(stdout, "Creating a thread to read from ICAROUS #%i\n", (i+1));
        icarousID[i] = std::thread(std::bind(&IcarousCommunicationService::ICAROUS_listener, this, i));
    }

    return (true);
};

// Listener for ICAROUS command messages
void IcarousCommunicationService::ICAROUS_listener(int id)
{
    int instanceIndex = id;
    fprintf(stdout, "This is icarous instance #%i\n", (instanceIndex + 1));
    int64_t icarousClientFd = client_sockfd[instanceIndex];
    fprintf(stdout, "instance #%i | icarousClientFd: %lli\n", (instanceIndex + 1), icarousClientFd);
    
    
    const int max_message_length = 87040;
    char messageBuffer[max_message_length + 1];
    
    // Listen to ICAROUS forever
    while(true){
        //fprintf(stdout, "Child listening to icarousClientFd: %lli\n", icarousClientFd);        
        
        messageBuffer[0] = '\0';
        int nread = max_message_length;
        int bytesReceived = 0;
        errno = 0;
        
        //listen to each client socket
        //Read any messages ICAROUS has posted
        
        while(nread == max_message_length && !errno){
            //fprintf(stdout, "Read call made in icarousClientFd %lli\n", icarousClientFd);
            nread = read(icarousClientFd, messageBuffer, max_message_length);
            bytesReceived += nread;
        }
        
        messageBuffer[bytesReceived] = '\0'; //makes sure we never segfault
        
        //fprintf(stdout, "UAV %i | Full message from child socket #%lli:\n%s\n", instanceIndex + 1, icarousClientFd, messageBuffer);
        
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
                char *modeType            = strncpy(throwaway, trackingHelper, fieldLength);


                //fprintf(stdout, "%lli|SETMOD|modeType|%s\n", icarousClientFd, modeType);


                if(!strncmp(modeType, "_ACTIVE_", strlen("_ACTIVE_"))) // ICAROUS has taken over, pause all tasks
                {
                    //fprintf(stderr, "UAV %i's last waypoint saved currentWaypointIndex[instanceIndex] = %lli as: %lli\n", (instanceIndex + 1), currentWaypointIndex[instanceIndex], icarousClientWaypointLists[instanceIndex][currentWaypointIndex[instanceIndex]]);
                    icarousTakeoverActive[instanceIndex] = true;
                    truncateWaypoint[instanceIndex] = false;
                    for(unsigned int taskIndex = 0; taskIndex < entityTasks[instanceIndex].size(); taskIndex++)
                    {
                        //fprintf(stderr, "UAV %i pausing task #%lli\n", (instanceIndex + 1), entityTasks[instanceIndex][taskIndex]);
                        auto pauseTask = std::make_shared<uxas::messages::task::TaskPause>();
                        pauseTask->setTaskID(entityTasks[instanceIndex][taskIndex]);
                        sendSharedLmcpObjectBroadcastMessage(pauseTask);
                    }
                }
                else if(!strncmp(modeType, "_PASSIVE_", strlen("_PASSIVE_"))) // ICAROUS has handed back control, resume all tasks
                {
                    //fprintf(stderr, "Sending UAV %i to its currentWaypointIndex[instanceIndex] = %lli last waypoint: %lli\n", (instanceIndex + 1), currentWaypointIndex[instanceIndex], icarousClientWaypointLists[instanceIndex][currentWaypointIndex[instanceIndex]]);
                    
                    // TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO
                    // TODO The issue is currently with a double-takeover event. When ICAROUS takes over a second     TODO
                    // TODO time, the set passive code bellow fails to work. Check into this using example 12-3.      TODO
                    // TODO A possible way to find this is to add print statements everywhere. Check the flag values! TODO
                    // TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO
                    // SOFT RESET ICAROUS (RESET_SFT)
                    // Send a message to ICAROUS to ensure that it soft-resets
                    // Possibly set a variable here to true to do that
                    softResetFlag[instanceIndex] = true;
                    sem_wait(&softResetSemaphores[instanceIndex]);
                    
                    fprintf(stderr, "UAV %i | after semaphore\n", instanceIndex + 1);
                    
                    for(unsigned int taskIndex = 0; taskIndex < entityTasks[instanceIndex].size(); taskIndex++)
                    {
                        //fprintf(stderr, "UAV %i resuming task #%lli\n", (instanceIndex + 1), entityTasks[instanceIndex][taskIndex]);
                        auto resumeTask = std::make_shared<uxas::messages::task::TaskResume>();
                        resumeTask->setTaskID(entityTasks[instanceIndex][taskIndex]);
                        sendSharedLmcpObjectBroadcastMessage(resumeTask);
                    }
                    icarousTakeoverActive[instanceIndex] = false;
                    
                    fprintf(stderr, "UAV %i | takeover is set to off\n", instanceIndex + 1);
                    
                    //fprintf(stdout, "UAV %i | FirstWaypoint before sending: %lli \n", instanceIndex + 1, missionCommands->getFirstWaypoint());
                    fprintf(stderr, "SENDING NEW MISSION COMMAND TO UAV %i!!!\n", instanceIndex + 1);
                    std::cout << missionCommands[instanceIndex]->toString() << std::endl;
                    sendSharedLmcpObjectBroadcastMessage(missionCommands[instanceIndex]);
                    resumePointSet[instanceIndex] = true;
                
                    // ARTIFACT -- Keeping just in case we need to revert
                    // Construct the new mission command here
                    // Create a waypoint list fromt the waypoints
                    // The current waypoint list will need to be changed back to icarous order to work better.
                    /*
                    auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
                    vehicleActionCommand->setVehicleID(instanceIndex + 1);
                    
                    auto goToWaypointAction = new afrl::cmasi::GoToWaypointAction;
                    goToWaypointAction->setWaypointNumber(icarousClientWaypointLists[instanceIndex][currentWaypointIndex[instanceIndex]]);
                    
                    vehicleActionCommand->getVehicleActionList().push_back(goToWaypointAction);
                    sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);
                    */
                }
                
                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else if(!strncmp(tempMessageBuffer, "SETPOS", 6))
            {
                // SETPOS,lat~,long~,alt~,\n
                //fprintf(stdout, "SETPOS message received in icarousClientFd %lli!\n", icarousClientFd);
                
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


                //fprintf(stdout, "%lli|SETPOS|latitude|%f\n", icarousClientFd, latitude);
                //fprintf(stdout, "%lli|SETPOS|longitude|%f\n", icarousClientFd, longitude);
                //fprintf(stdout, "%lli|SETPOS|altitude|%f\n", icarousClientFd, altitude);


                auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
                vehicleActionCommand->setVehicleID(instanceIndex + 1);

                auto loiterAction = new afrl::cmasi::LoiterAction;
                auto location3d = new afrl::cmasi::Location3D;
                location3d->setLatitude(latitude);
                location3d->setLongitude(longitude);
                location3d->setAltitude(altitude);
                loiterAction->setLocation(location3d);

                vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
                sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);


                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else if(!strncmp(tempMessageBuffer, "SETVEL", 6))
            {
                // SETVEL,u~,v~,w~,\n
                //fprintf(stdout, "SETVEL message received in icarousClientFd %lli!\n", icarousClientFd);
                
                // Get u
                trackingHelper            = strstr(tempMessageBuffer, "north");
                trackingHelper           += 5; //skip past "north"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float north     = atof(strncpy(throwaway, trackingHelper, fieldLength));

                // Get v
                trackingHelper            = strstr(tempMessageBuffer, "east");
                trackingHelper           += 4; //skip past "east"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float east     = atof(strncpy(throwaway, trackingHelper, fieldLength));

                // Get w
                trackingHelper            = strstr(tempMessageBuffer, "down");
                trackingHelper           += 4; //skip past "down"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float down     = atof(strncpy(throwaway, trackingHelper, fieldLength));
                
                
                //fprintf(stdout, "%lli|SETVEL|north|%f\n", icarousClientFd, north);
                //fprintf(stdout, "%lli|SETVEL|east|%f\n", icarousClientFd, east);
                //fprintf(stdout, "%lli|SETVEL|down|%f\n", icarousClientFd, down);

                
                //fprintf(stdout, "Starting creationg of VehicleActionCommand message\n");                
                auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
                vehicleActionCommand->setVehicleID(instanceIndex + 1);
                
                if((north == 0) && (east == 0)) // loiter at this location
                {
                    //fprintf(stdout, "Start of LoiterAction construction\n");
                    auto loiterAction =  new afrl::cmasi::LoiterAction;
                    auto location3d = new afrl::cmasi::Location3D;
                    currentInformationMutexes[instanceIndex].lock();
                    location3d->setLatitude(currentInformation[instanceIndex][1]);
                    location3d->setLongitude(currentInformation[instanceIndex][2]);
                    location3d->setAltitude(down + currentInformation[instanceIndex][3]);
                    currentInformationMutexes[instanceIndex].unlock();
                    loiterAction->setLocation(location3d);
                    
                    vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
                    //fprintf(stdout, "End of LoiterAction setup\n");
                }
                else // otherwise set a FlightDirectorAction to move in a certain direction
                {
                    //fprintf(stdout, "Start of FlightDirectorAction construction");
                    auto flightDirectorAction = new afrl::cmasi::FlightDirectorAction;
                    double actualSpeed = sqrt(pow(north,2)+pow(east,2));
                    flightDirectorAction->setSpeed(actualSpeed);
                    double heading = acos(north / sqrt(pow(north, 2) + pow(east, 2)));

                    if((north > 0) && (east > 0)){
                        heading = 90 - heading;
                    }
                    else if((north > 0) && (east < 0))
                    {
                        heading = -90 + heading;
                    }
                    else if((north < 0) && (east < 0))
                    {
                        heading = -180 + heading;
                    }
                    else if((north < 0) && (east > 0))
                    {
                        heading = 180 - heading;
                    }

                    //fprintf(stdout, "Heading Set | Current Altitude: %f | Setting Altitude\n", currentInformation[instanceIndex][3]);
                    flightDirectorAction->setHeading(heading);
                    flightDirectorAction->setClimbRate(-down);
                    //fprintf(stdout, "Altitude Set | Adding to VehicleActionCommand\n");
                    
                    vehicleActionCommand->getVehicleActionList().push_back(flightDirectorAction);
                    //fprintf(stdout, "End of FlightDirectorAction setup\n");
                }
                
                //std::cout << vehicleActionCommand->getVehicleActionList().front()->toString() << std::endl;;
                
                sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);
                //fprintf(stdout, "VehicleActionCommand sent\n");
                
                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else if(!strncmp(tempMessageBuffer, "GOTOWP", 6))
            {
                // GOTOWP,id~,\n
                //fprintf(stdout, "GOTOWP message received in icarousClientFd %lli!\n", icarousClientFd);
                
                // Get id
                trackingHelper            = strstr(tempMessageBuffer, "id");
                trackingHelper           += 2; //skip past "id"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                int id     = atof(strncpy(throwaway, trackingHelper, fieldLength));
                // Add one to make the index correct
                id++;
                
                
                //fprintf(stdout, "%lli|GOTOWP|id|%i\n", icarousClientFd, id);

                
                auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
                vehicleActionCommand->setVehicleID(instanceIndex + 1);
                
                auto goToWaypointAction = new afrl::cmasi::GoToWaypointAction;
                goToWaypointAction->setWaypointNumber(icarousClientWaypointLists[instanceIndex][id]);
                
                vehicleActionCommand->getVehicleActionList().push_back(goToWaypointAction);
                sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);
                
                
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
        
        //fprintf(stderr, "About to read again\n");
    }
}


// This function is performed to cleanly terminate the service
bool IcarousCommunicationService::terminate()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    // rejoin all threads on the programs end
    for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
    {
        icarousID[i].join();
    }
    
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
        // (so when using it as an index, it should be [vehicleID - 1])
        auto vehicleID = ptr_MissionCommand->getVehicleID();
        std::cout << "Vehicle ID is " << vehicleID << "\n";
        
        // Check that the vehicle has not already recieved its waypoints
        if (!has_gotten_waypoints[vehicleID - 1])
        {
            // Set the variable to ensure we only send one vehicle one MissionCommand
            has_gotten_waypoints[vehicleID - 1] = true;
            //fprintf(stdout, "Sending waypoints to ICAROUS instance %lld\n", vehicleID);
            
            // Set up variable to be used
            int waypointIndex = (ptr_MissionCommand->getFirstWaypoint() - 1);
            int totalNumberOfWaypoints = 0;
            int nextWaypoint = ptr_MissionCommand->getWaypointList()[waypointIndex]->getNextWaypoint();

            icarousClientWaypointLists[vehicleID - 1].resize(ptr_MissionCommand->getWaypointList().size());
            
            missionCommands[vehicleID - 1] = ptr_MissionCommand;

            // For each waypoint in the mission command, send each as its own message to ICAROUS
            // The last waypoint's next value will be equal to itself (This indicates the end)
            while(nextWaypoint != (ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber()))
            {
                totalNumberOfWaypoints++;
                
                //fprintf(stdout, "WaypointIndex: %i | nextWaypoint: %i\n", waypointIndex, nextWaypoint);
                //fprintf(stdout, "Sending a waypoint to ICAROUS[%i]\n", client_sockfd[vehicleID-1]);

                // Actually set up the message to send using dprintf and send along the socket
                dprintf(client_sockfd[vehicleID - 1], "WAYPT,total%i.0,speed%f,lat%f,long%f,alt%f,index%lld.0,\n",
                    totalNumberOfWaypoints,
                    ptr_MissionCommand->getWaypointList()[waypointIndex]->getSpeed(),
                    ptr_MissionCommand->getWaypointList()[waypointIndex]->getLatitude(),
                    ptr_MissionCommand->getWaypointList()[waypointIndex]->getLongitude(), 
                    ptr_MissionCommand->getWaypointList()[waypointIndex]->getAltitude(),
                    (ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber() - ptr_MissionCommand->getFirstWaypoint()));
                
                // Need to convert numbers to the indexes
                // Then store the lat long and alt of each waypoint
                // This is to put them all into an ordered list
                icarousClientWaypointLists[vehicleID - 1][totalNumberOfWaypoints - 1] = ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber();
                newWaypointLists[vehicleID - 1].push_back(ptr_MissionCommand->getWaypointList()[waypointIndex]);
                //fprintf(stderr, "UAV %lli | Stored index %i as %lli\n", vehicleID, (totalNumberOfWaypoints - 1), ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber());
                //fprintf(stdout, "WP|%lli\n", icarousClientWaypointLists[vehicleID - 1][totalNumberOfWaypoints - 1].getNumber());
                
                // Set the index of the next waypoint
                waypointIndex = (nextWaypoint - 1);

                // Grab the next waypoint's next waypoint to check if it is the end
                nextWaypoint = ptr_MissionCommand->getWaypointList()[waypointIndex]->getNextWaypoint();
            }
            
            // Need to ensure the last waypoint is also sent
            totalNumberOfWaypoints++;
            dprintf(client_sockfd[vehicleID - 1], "WAYPT,total%i.0,speed%f,lat%f,long%f,alt%f,index%lld.0,\n",
                totalNumberOfWaypoints,
                ptr_MissionCommand->getWaypointList()[waypointIndex]->getSpeed(),
                ptr_MissionCommand->getWaypointList()[waypointIndex]->getLatitude(),
                ptr_MissionCommand->getWaypointList()[waypointIndex]->getLongitude(), 
                ptr_MissionCommand->getWaypointList()[waypointIndex]->getAltitude(),
                (ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber() - ptr_MissionCommand->getFirstWaypoint()));
            
            icarousClientWaypointLists[vehicleID - 1][totalNumberOfWaypoints - 1] = ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber();
            //fprintf(stderr, "UAV %lli | Stored index %i as %lli\n", vehicleID, (totalNumberOfWaypoints - 1), ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber());
            
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
            dprintf(client_sockfd[i], "COMND,type%s,\n",//,id%lld.0,\n",
            "GEOFN_SEND");//,
            //ptr_Zone->getZoneID());
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
        
        // Get the current tasks and update the list (Only when ICAROUS does not have control)
        if(icarousTakeoverActive[vehicleID - 1] == false){
            entityTasks[vehicleID - 1] = ptr_AirVehicleState->getAssociatedTasks();
            
            //positionBeforeTakeover[vehicleID - 1][0] = ptr_AirVehicleState->getHeading(); // First value is not needed
            positionBeforeTakeover[vehicleID - 1][1] = ptr_AirVehicleState->getLocation()->getLatitude();
            positionBeforeTakeover[vehicleID - 1][2] = ptr_AirVehicleState->getLocation()->getLongitude();
            positionBeforeTakeover[vehicleID - 1][3] = ptr_AirVehicleState->getLocation()->getAltitude();
            
            // Updates the current waypoint to the waypoint the UAV is currently doing
            // Also saves this waypoint to be compared to the next to ensure that a change of waypoints is seen
            if(isLastWaypointInitialized[vehicleID - 1]) // && (lastWaypoint[vehicleID - 1] != ptr_AirVehicleState->getCurrentWaypoint()))
            {
                //        So the currentWaypoint that shows up from an AirVehicleState may skip passed some waypoints
                //        provided that they are close enough together. This causes an issue with the bellow code because
                //        it needs to:
                //        1.) Send all reached waypoints to ICAROUS so that ICAROUS does not route back to an old waypoint
                //        2.) Keep track of the index ICAROUS is at when looking at waypoints
                
                while(currentWaypointIndex[vehicleID - 1] < (ptr_AirVehicleState->getCurrentWaypoint() - missionCommands[vehicleID - 1]->getFirstWaypoint())){
                  resumePointSet[vehicleID - 1] = false;
                    dprintf(client_sockfd[vehicleID - 1], "WPRCH,id%lli.0,\n",
                       currentWaypointIndex[vehicleID - 1]);
                    
                    //dprintf(1, "UAV %i | WPRCH,id%lli.0,\n",
                    //    vehicleID,
                    //    currentWaypointIndex[vehicleID - 1]);
                    
                    currentWaypointIndex[vehicleID - 1]++;
                    
                    if(truncateWaypoint[vehicleID - 1] == true){
                        //fprintf(stderr, "UAV %i | Truncating waypoint index [%lli]\n", vehicleID, currentWaypointIndex[vehicleID - 1]);
                        newWaypointLists[vehicleID - 1].erase(newWaypointLists[vehicleID - 1].begin());
                    }else{
                        //fprintf(stderr, "UAV %i | Skipping truncation\n", vehicleID);
                        truncateWaypoint[vehicleID - 1] = true;
                    }
                    
                    if(lastWaypoint[vehicleID - 1] == ptr_AirVehicleState->getCurrentWaypoint()){
                        //fprintf(stdout, "UAV %i | lastwaypoint indicates task is finished\n", vehicleID);
                    }else{
                        //fprintf(stdout, "UAV %i | lastwaypoint is moving up one\n", vehicleID);
                        lastWaypoint[vehicleID - 1]++;
                    }
                    sleep(0.1);
                }
                //fprintf(stdout, "UAV %i | currentWaypointIndex %lli | getCurrentWaypoint() %lli\n", vehicleID, currentWaypointIndex[vehicleID - 1], (ptr_AirVehicleState->getCurrentWaypoint()));
                //currentWaypointIndex[vehicleID - 1] = (ptr_AirVehicleState->getCurrentWaypoint() - missionCommands[vehicleID - 1]->getFirstWaypoint());
            }
            else
            {
                //fprintf(stdout, "Reseting lastWaypoint and currentWaypointIndex\n");
                isLastWaypointInitialized[vehicleID - 1] = true;
                lastWaypoint[vehicleID - 1] = 0;//ptr_AirVehicleState->getCurrentWaypoint();
                currentWaypointIndex[vehicleID - 1] = 0;
            }
            
            //fprintf(stderr, "UAV %i | lastWaypoint: %lli | currentWaypointIndex: %lli\n", vehicleID, lastWaypoint[vehicleID - 1], currentWaypointIndex[vehicleID - 1]);
        }


        currentInformationMutexes[vehicleID - 1].lock();
        /*
        fprintf(stdout, "UAV %i | Heading %f | Lat %f | Long %f | Alt %f\n      | Heading %f | Lat %f | Long %f | Alt %f",
            vehicleID,
            ptr_AirVehicleState->getHeading(),
            ptr_AirVehicleState->getLocation()->getLatitude(),
            ptr_AirVehicleState->getLocation()->getLongitude(),
            ptr_AirVehicleState->getLocation()->getAltitude(),
            currentInformation[vehicleID - 1][0],
            currentInformation[vehicleID - 1][1],
            currentInformation[vehicleID - 1][2],
            currentInformation[vehicleID - 1][3]);
        */
        currentInformation[vehicleID - 1][0] = ptr_AirVehicleState->getHeading();
        currentInformation[vehicleID - 1][1] = ptr_AirVehicleState->getLocation()->getLatitude();
        currentInformation[vehicleID - 1][2] = ptr_AirVehicleState->getLocation()->getLongitude();
        currentInformation[vehicleID - 1][3] = ptr_AirVehicleState->getLocation()->getAltitude();
        currentInformationMutexes[vehicleID - 1].unlock();
        
        
        
        // ptr_AirVehicleState->getU()
        // ptr_AirVehicleState->getV()
        // ptr_AirVehicleState->getW()
        
        // heading = (ptr_AirVehicleState->getHeading() + 360) % 360
        
        // u's heading: heading
        // u's north contribution: [0, u] Continuous
        // u's north sign: [-1, 1] Discrete
        // u's east contribution: [0, u] Continuous
        // u's east sign: [-1, 1] Discrete
        
        // v's heading: (heading + 90) % 360
        // v's north contribution: [0, u] Continuous
        // v's north sign: [-1, 1] Discrete
        // v's east contribution: [0, u] Continuous
        // v's east sign: [-1, 1] Discrete
        
        // TODO - This needs re-worked to account for pitch angle
        
        double uHeading = fmod((ptr_AirVehicleState->getHeading() + 360), 360.0);
        double vHeading = fmod((uHeading + 90), 360.0);
        double uNorth;
        double vNorth;
        double uEast;
        double vEast;
        // TODO - May need to fiddle with this to be correct (Not sure if implemented positive up or down in ICAROUS)
        double wDown = ptr_AirVehicleState->getW();
        
        
        uNorth = (1 - ((fmod(uHeading, 90.0)) / 90)) * ptr_AirVehicleState->getU();
        uEast = ((fmod(uHeading, 90)) / 90.0) * ptr_AirVehicleState->getU();
        
        vNorth = (1 - ((fmod(vHeading, 90.0)) / 90)) * ptr_AirVehicleState->getV();
        vEast = ((fmod(vHeading, 90.0)) / 90) * ptr_AirVehicleState->getV();
        
        if(uHeading < 90){
            uNorth = fabs(uNorth);
            uEast = fabs(uEast);
            vNorth = fabs(vNorth) * -1;
            vEast = fabs(vEast);
        }else if(uHeading >= 90 && uHeading < 180){
            uNorth = fabs(uNorth) * -1;
            uEast = fabs(uEast);
            vNorth = fabs(vNorth) * -1;
            vEast = fabs(vEast) * -1;
        }else if(uHeading >= 180 && uHeading < 270){
            uNorth = fabs(uNorth) * -1;
            uEast = fabs(uEast) * -1;
            vNorth = fabs(vNorth);
            vEast = fabs(vEast) * -1;
        }else{
            uNorth = fabs(uNorth);
            uEast = fabs(uEast) * -1;
            vNorth = fabs(vNorth);
            vEast = fabs(vEast);
        }
        
        double northTotal = uNorth + vNorth;
        double eastTotal = uEast + vEast;
        double downTotal = wDown;
        
        /*
        fprintf(stdout, "UAV: %i\n", vehicleID);
        fprintf(stdout, "North is: %f\n", northTotal);
        fprintf(stdout, "East is: %f\n", eastTotal);
        fprintf(stdout, "Down is: %f\n", downTotal);
        fprintf(stderr, "\n");
        */


        dprintf(client_sockfd[vehicleID - 1], "POSTN,timegps%f,lat%f,long%f,altabs%f,altrel%f,north%f,east%f,down%f,hdop%f,vdop%f,numsats%i.0,id%i.0,\n",
            ((double)ptr_AirVehicleState->getTime()/1000),
            ptr_AirVehicleState->getLocation()->getLatitude(),
            ptr_AirVehicleState->getLocation()->getLongitude(),
            ptr_AirVehicleState->getLocation()->getAltitude(),
            ptr_AirVehicleState->getLocation()->getAltitude(),// TODO - come back to this, rel altitude != abs altitude
            northTotal,
            eastTotal,
            downTotal,
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
                dprintf(client_sockfd[i], "OBJCT,type%s,lat%f,long%f,alt%f,north%f,east%f,down%f,index%i.0,\n",
                    "_TRAFFIC_",//either _TRAFFIC_ or _OBSTACLE_
                    ptr_AirVehicleState->getLocation()->getLatitude(),
                    ptr_AirVehicleState->getLocation()->getLongitude(),
                    ptr_AirVehicleState->getLocation()->getAltitude(),
                    northTotal,
                    eastTotal,
                    downTotal,
                    vehicleID); // ICAROUS indexes start at 1 normally
            }
        }

        if((softResetFlag[vehicleID - 1] == true) && (resumePointSet[vehicleID - 1] == false))
        {
            // TODO - Make it so it was the last place the UAV was before ICAROUS took over
            
            // Tell ICAROUS to initiate a soft-reset
            dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,lat%f,long%f,alt%f,\n",
                "RESET_SFT",
                ptr_AirVehicleState->getLocation()->getLatitude(),
                ptr_AirVehicleState->getLocation()->getLongitude(),
                ptr_AirVehicleState->getLocation()->getAltitude());
            
            // Set new waypoint information
            
            // At this point, the last waypoint is actually the current waypoint.
            // Thus, we need to subtract one to make it the last waypoint.
            
            //std::cout << missionCommands[vehicleID - 1]->toString() << std::endl;
            //missionCommands[vehicleID - 1]->setFirstWaypoint(icarousClientWaypointLists[vehicleID - 1][lastWaypoint[vehicleID - 1]]);
            //std::cout << missionCommands[vehicleID - 1]->toString() << std::endl;
            /*
            for(unsigned int i = 0; i < icarousClientWaypointLists[vehicleID - 1].size(); i++){
                fprintf(stderr, "UAV %i | icarousClientWaypointLists %lli\n", vehicleID, icarousClientWaypointLists[vehicleID - 1][i]);
            }
            */
            //int indexOfWaypointToReplace = icarousClientWaypointLists[vehicleID - 1][currentWaypointIndex[vehicleID - 1] - 1] - 1;
            
            //fprintf(stdout, "UAV %i | Replacing waypoint %i at index %lli\n", vehicleID, indexOfWaypointToReplace, currentWaypointIndex[vehicleID - 1] - 1);
            
            newWaypointLists[vehicleID - 1][0]->setLatitude(
                positionBeforeTakeover[vehicleID - 1][1]);
            
            newWaypointLists[vehicleID - 1][0]->setLongitude(
                positionBeforeTakeover[vehicleID - 1][2]);
            
            newWaypointLists[vehicleID - 1][0]->setAltitude(
                positionBeforeTakeover[vehicleID - 1][3]);
            
            missionCommands[vehicleID - 1]->setFirstWaypoint(newWaypointLists[vehicleID - 1][0]->getNumber());
            
            missionCommands[vehicleID - 1]->setCommandID(0);
            
            missionCommands[vehicleID - 1]->getWaypointList().clear();
            
            missionCommands[vehicleID - 1]->getWaypointList().push_back(newWaypointLists[vehicleID - 1][0]);
            
            for(unsigned int i = 0; i < newWaypointLists[vehicleID - 1].size(); i++){
                //fprintf(stderr, "UAV %i | Setting waypointList at %i to %lli\n", vehicleID, i, newWaypointLists[vehicleID - 1][i]->getNumber());
                missionCommands[vehicleID - 1]->getWaypointList().push_back(newWaypointLists[vehicleID - 1][i]);
            }
            
            std::cout << missionCommands[vehicleID - 1]->toString() << std::endl;
            
            //fprintf(stderr, "UAV %i | current %lli | last %lli\n", vehicleID, currentWaypointIndex[vehicleID - 1], lastWaypoint[vehicleID - 1]);
            
            //isLastWaypointInitialized[vehicleID - 1] = false;
            softResetFlag[vehicleID - 1] = false;
            sem_post(&softResetSemaphores[vehicleID - 1]);
        }else if((softResetFlag[vehicleID - 1] == true) && (resumePointSet[vehicleID - 1] == true)){
            // Otherwise if we already have a waypoint set, continue the mission
            softResetFlag[vehicleID - 1] = false;
            sem_post(&softResetSemaphores[vehicleID - 1]);
        }
    }// End of AirVehicleState


    // False indicates that we are ready to process more messages
    return false;
}
}; //namespace service
}; //namespace uxas

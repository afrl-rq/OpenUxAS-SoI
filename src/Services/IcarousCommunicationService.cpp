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
 * <Service Type="IcarousCommunicationService" NumberOfUAVs="n" />
 * 
 * This file allows connectivity with the ICAROUS system
 * (CRoss Application Translator of Operational Unmanned Systems) 
 * ICAROUS allows cooperative mission planning between UxAS and ICAROUS
 * 
 *
 *  Things still to do:
 *   TODO - Use UxAS logging function and UxAS print statements
 *
 *   TODO processReceivedLmcpMessage - Find if there is a place to get relative altitude from AMASE for the UAVs position
 *                                     Currently, only one is stored; not sure if this is possible
 *   TODO processReceivedLmcpMessage - Locate a place where horizonal accuracy is defined (hdop)
 *   TODO processReceivedLmcpMessage - Locate a place where vertical accuracy is defined (vdop)
 *   TODO processReceivedLmcpMessage - Find a way to get the yaw from AMASE for a given UAV (not default included in the message)
 *   
 *
 *  Notes:
 *   This code ONLY works on Linux, since it uses Linux function calls (dprintf)
 *   Built and tested on Ubuntu 16.04 32-bit with ICAROUS 2.1
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
#include "afrl/cmasi/AirVehicleConfiguration.h"
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

// Unsure if needed
//#include "uxas/messages/route/RoutePlan.h"


#include "uxas/messages/task/TaskPause.h"
#include "uxas/messages/task/TaskResume.h"
#include "uxas/messages/uxnative/IncrementWaypoint.h"

#include "Constants/UxAS_String.h"

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

    // Number of UAVs to be controled by ICAROUS
    if (!ndComponent.attribute(STRING_XML_ICAROUS_CONNECTIONS).empty())
    {
        ICAROUS_CONNECTIONS = ndComponent.attribute(STRING_XML_ICAROUS_CONNECTIONS).as_int();
    }
    else
    {
        fprintf(stderr, "Number of UAVs not specified!\nTry to use a string such as:\t<Service Type=\"IcarousCommunicationService\" NumberOfUAVs=\"2\" /> in the XML.\n");
        isSuccess = false;
    }
    
    // Which routePlanner ICAROUS should use (if specified, otherwise use UxAS visibility planner)
    if (!ndComponent.attribute(STRING_XML_ICAROUS_ROUTEPLANNER).empty())
    {
        ICAROUS_ROUTEPLANNER = ndComponent.attribute(STRING_XML_ICAROUS_ROUTEPLANNER).as_int();
    }// If not specified, do not use (-1 option is default)

    // Which routePlanner ICAROUS should use (if specified, otherwise use UxAS visibility planner)
    if (!ndComponent.attribute(STRING_XML_ICAROUS_DEVIATION_ORIGIN).empty())
    {
        DEVIATION_ORIGIN = ndComponent.attribute(STRING_XML_ICAROUS_DEVIATION_ORIGIN).as_string();
    }// If not specified, do not use (-1 option is default)    

    // Define the distance a UAV can travel away from its path and still continue the mission
    if (!ndComponent.attribute(STRING_XML_LINE_VOLUME).empty())
    {
        LINE_VOLUME = ndComponent.attribute(STRING_XML_LINE_VOLUME).as_int();
        if(DEVIATION_ORIGIN == "line"){
            // TODO - Need to actually take into account the distance from the line in deviation amounts.
            //        This will require checking the search that is being done, and checking distances based on that.
            //        Something to note is that deviation will be 200 meters less then specified to keep the UAV a
            //        safe distance from the line. Negative deviation or zero indicate no deviation is allowed.
            LINE_VOLUME = LINE_VOLUME - 200;
        }
        else if(DEVIATION_ORIGIN == "path")
        {
            // LINE_VOLUME stays the same.
        }
    }// If not specified, use 500m

    // Used to notify ICAROUS of path plans
    addSubscriptionAddress(uxas::common::MessageGroup::IcarousPathPlanner());

    // RoutePlanRequest messages are used for if a route plan is given and we want to use ICAROUS route planners
    addSubscriptionAddress(uxas::messages::route::RoutePlanRequest::Subscription);
    
    // MissionCommand messages are used to determine where a singular UAV is going to go during a mission
    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    
    // KeepInZone messages are used to define all zones to stay within
    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    
    // KeepOutZone messages are used to define all zones to stay out of
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    
    // AirVehicleStates are returned from OpenAMASE to know where a UAV is and what it is doing
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    
    // Need the aircraft's nominal speed from this
    addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
    
    return (isSuccess);
}



// Start up the module, initialize variables, and connect to ICAROUS instance(s)
bool IcarousCommunicationService::initialize()
{
    // Perform any required initialization before the service is started
    //std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;


    // -- Variable set-up --

    // Set vectors to the Number of UAVs specified in the XML
    // Variable uses are defined in the header file
    client_sockfd.resize(ICAROUS_CONNECTIONS);
    currentInformation.resize(ICAROUS_CONNECTIONS);
    currentWaypointIndex.resize(ICAROUS_CONNECTIONS);
    deviationFlags.resize(ICAROUS_CONNECTIONS);
    entityTasks.resize(ICAROUS_CONNECTIONS);
    has_gotten_waypoints.resize(ICAROUS_CONNECTIONS);
    headingLists.resize(ICAROUS_CONNECTIONS);
    icarousClientWaypointLists.resize(ICAROUS_CONNECTIONS);
    icarousID.resize(ICAROUS_CONNECTIONS);
    icarousTakeoverActive.resize(ICAROUS_CONNECTIONS);
    isLastWaypointInitialized.resize(ICAROUS_CONNECTIONS);
    isRoutePlanResponseInit.resize(ICAROUS_CONNECTIONS);
    lastWaypoint.resize(ICAROUS_CONNECTIONS);
    messageQueue.resize(ICAROUS_CONNECTIONS);
    missionCommands.resize(ICAROUS_CONNECTIONS);
    newWaypointLists.resize(ICAROUS_CONNECTIONS);
    noDeviationReset.resize(ICAROUS_CONNECTIONS);
    nominalUAVHorizontalSpeed.resize(ICAROUS_CONNECTIONS);
    nominalUAVVerticleSpeed.resize(ICAROUS_CONNECTIONS);
    originalStartingWaypoint.resize(ICAROUS_CONNECTIONS);
    positionBeforeTakeover.resize(ICAROUS_CONNECTIONS);
    resumePointSet.resize(ICAROUS_CONNECTIONS);
    routePlanCounter.resize(ICAROUS_CONNECTIONS);
    routePlanRequests.resize(ICAROUS_CONNECTIONS);
    routePlanResponses.resize(ICAROUS_CONNECTIONS);
    routePlanWaypointCounter.resize(ICAROUS_CONNECTIONS);
    routePlans.resize(ICAROUS_CONNECTIONS);
    softResetFlag.resize(ICAROUS_CONNECTIONS);
    truncateWaypoint.resize(ICAROUS_CONNECTIONS);
    waitingForResponse.resize(ICAROUS_CONNECTIONS);

    
    // Mutexes & Semaphores must be set like this and not in a vector
    // This is because a vector of these objects is non-resizable
    // These objects cannot be deleted without causing an issue, 
    // thus resizing like the above is impossible
    currentInformationMutexes = new std::mutex[ICAROUS_CONNECTIONS];
    deviationMutex = new std::mutex[ICAROUS_CONNECTIONS];
    messageQueueMutex = new std::mutex[ICAROUS_CONNECTIONS];
    softResetSemaphores = new sem_t[ICAROUS_CONNECTIONS];
    
    // Some vectors are subvectors and need additional initialization of size
    for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
    {
        // This is to set the size of heading, lat, long, and alt for each instance
        currentInformation[i].resize(4);
        positionBeforeTakeover[i].resize(4);
        
        // Also need to initialize all the semaphores to 0
        sem_init(&softResetSemaphores[i], 0, 0);
    }

    // Need to initialize all variables that can be initialized at this point
    // Some of the other vectors values are initialized later in the program at the earliest convienience
    deviationFlags.assign(ICAROUS_CONNECTIONS, false);
    has_gotten_waypoints.assign(ICAROUS_CONNECTIONS, false);
    icarousTakeoverActive.assign(ICAROUS_CONNECTIONS, false);
    isLastWaypointInitialized.assign(ICAROUS_CONNECTIONS, false);
    isRoutePlanResponseInit.assign(ICAROUS_CONNECTIONS, false);
    noDeviationReset.assign(ICAROUS_CONNECTIONS, false);
    resumePointSet.assign(ICAROUS_CONNECTIONS, false);
    softResetFlag.assign(ICAROUS_CONNECTIONS, false);
    truncateWaypoint.assign(ICAROUS_CONNECTIONS, false);
    waitingForResponse.assign(ICAROUS_CONNECTIONS, false);

    currentWaypointIndex.assign(ICAROUS_CONNECTIONS, 0);
    lastWaypoint.assign(ICAROUS_CONNECTIONS, -1);
    routePlanCounter.assign(ICAROUS_CONNECTIONS, 0);
    routePlanWaypointCounter.assign(ICAROUS_CONNECTIONS, 1);

    
    // Protocol constants for 3-way ICAROUS authentication handshake    
    const char *protocol1 = "ICAROUS-UxAS_LMCP";
    const char *protocol2 = "ok ";
    const char *sharedSecret = "28a4b77b86aa32715e4c271415b28447b8c08d704fd9ffb1258bced7b7167fe0";
    const char *err = "error";
    
    // Other variables needed for socket setup
    int server_sockfd = -2;
    int i = 1;
    int nread;
    int nwrite;
    char buffer[strlen(sharedSecret) + 1];
        
    // Set up an IPv4 socket & make it stream-based and close on exec
    socklen_t server_len;
    struct sockaddr_in server_address;
    server_sockfd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    
    // Check to make sure that the socket was created successfully
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
            // Password reading was interupted in some way
            fprintf(stderr, "Fatal error, could not read ICAROUS password!\n");
            close(client_sockfd[connectionNum]);
            return false;
        }
        else if(!strcmp(sharedSecret, buffer)) // !compare==true indicates the strings are the same
        {
            // Password was acepted and recognized
            // Respond back to ICAROUS instance to inform it of the connection status
            if((write(client_sockfd[connectionNum], protocol2, strlen(protocol2))) <= 0)
            {
                // If there was an error with informming ICAROUS, error out
                fprintf(stderr, "Fatal error, write confirmation to ICAROUS failed!\n");
                close(client_sockfd[connectionNum]);
                return false;
            }
            
            // ICAROUS has been accepted, begin communication
            fprintf(stdout, "ICAROUS[%i] has connected to UxAS!\n", client_sockfd[connectionNum]);
        }
        else
        {
            // Password was rejected or another error was encountered
            nwrite = write(client_sockfd[connectionNum], err, strlen(err));
            fprintf(stderr, "Able to write %i bytes to ICAROUS reporting an error.\n", nwrite);
            close(client_sockfd[connectionNum]);
            return false;
        }
    }
    
    // Initialization was successful
    return true;
}



// This function is used to start the service and the ICAROUS listening side of the program
bool IcarousCommunicationService::start()
{
    // perform any actions required at the time the service starts
    //std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;


    // Start threads here to begin reading from ICAROUS instances
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
    // grab the ID from the handler (TODO - Verify if the variable 'id' is changed after other threads are started)
    int instanceIndex = id;
    //fprintf(stdout, "This is icarous instance #%i\n", (instanceIndex + 1));
    
    // grad the ICAROUS instances' socket for reading
    int64_t icarousClientFd = client_sockfd[instanceIndex];
    //fprintf(stdout, "instance #%i | icarousClientFd: %lli\n", (instanceIndex + 1), icarousClientFd);
    
    // Set the max message length and create a buffer to store messages of this size (TCP socket buffer maximum)
    const int max_message_length = 65535;
    char messageBuffer[max_message_length + 1];
    
    // Listen to ICAROUS instance forever
    while(true)
    {
        // DEBUG STATEMENT - Prints that we have started a new itteration
        //fprintf(stdout, "UAV &i | Child listening to icarousClientFd: %lli\n", instanceIndex + 1, icarousClientFd);        
        
        // Variables reset upon each read
        messageBuffer[0] = '\0';
        int nread = max_message_length;
        int bytesReceived = 0;
        errno = 0;
        
        // Listen to each client socket
        // Read any messages ICAROUS has posted
        while(nread == max_message_length && !errno){
            // DEBUG STATEMENT - Prints that a read call was made
            //                   Used to determine how many times an instance reads from the socket
            //fprintf(stdout, "UAV %i | Read call made in icarousClientFd %lli\n", instanceIndex + 1, icarousClientFd);
            nread = read(icarousClientFd, messageBuffer, max_message_length);
            bytesReceived += nread;
        }
        
        // Makes sure we never segfault
        messageBuffer[bytesReceived] = '\0';
        
        // DEBUG STATEMENT - Used for checking what the current message that was sent was
        //fprintf(stdout, "UAV %i | Full message from child socket #%lli:\n%s\n", instanceIndex + 1, icarousClientFd, messageBuffer);
        
        // Get a pointer to the message so as to not edit the original directly
        char *tempMessageBuffer = messageBuffer;
        
        // Process as many messages as where recieved
        while(strlen(tempMessageBuffer))
        {
        
            // Necessary variables for parsing the message
            char *fieldEnd;
            char throwaway[400]; // Used simply to fill necessary (but useless) arguments in function calls
            int fieldLength;
            char *trackingHelper;

            // START OF MESSAGE PROCESSING FROM ICAROUS
            
            /*
            // Sending to ICAROUS template
            if(!strncmp(tempMessageBuffer, "<type>", <type length>)) // <type description>
            {
                // MESSAGE STRUCTURE - <type structure>
                
                // The following section of code finds several fields by their tags.
                // It's fairly difficult to follow, so here's a comment section explaining each line.            
                 1. strstr returns a pointer to the first occurence of our tag in the message
                 * 2. Use pointer arithmetic to skip past the tag
                 * 3. Find the end of the field (they're variable length) using the ',' delimiter
                 * 4. Get the length of the field via pointer arithmetic (end - beginning)
                 * 5. Convert the field to a usable number and store it into the message to be published to cFS
                 
                // Note: We tried to functionize this code. We spent 4 hours and had the strangest
                // issue we've ever seen, with a passed-in pointer being invalid memory to access.
                // Possible it was a unique issue. (TODO - Possibly try this again?)

                // Mode type
                trackingHelper            = strstr(tempMessageBuffer, "<information header>");
                trackingHelper           += <length of <information header>>; // skip past "<information header>"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                char *<information>       = strncpy(throwaway, trackingHelper, fieldLength);

                // Other information parsing can go here
                
                // Processing code goes here
                
                // Generally these also send:
                sendSharedLmcpObjectBroadcastMessage(<message variable here>);
                // This should check is it is a valid message type
                
                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else
            */
            
            if(!strncmp(tempMessageBuffer, "SETMOD", 6)) // Set Mode (has ICAROUS taken over?)
            {
                // MESSAGE STRUCTURE - SETMOD,type~,\n
                
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
                // Possible it was a unique issue. (TODO - Possibly try this again?)

                // Mode type
                trackingHelper            = strstr(tempMessageBuffer, "type");
                trackingHelper           += 4; // skip past "type"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                char *modeType            = strncpy(throwaway, trackingHelper, fieldLength);

                // DEBUG STATEMENT - Print the contents of the message
                //fprintf(stdout, "%lli|SETMOD|modeType|%s\n", icarousClientFd, modeType);

                // ICAROUS has taken over
                if(!strncmp(modeType, "_ACTIVE_", strlen("_ACTIVE_")))
                {
                    printf("UAV %i | active\n", instanceIndex + 1);
                    // Inform other parts of the code that a take-over has started
                    icarousTakeoverActive[instanceIndex] = true;
                    // Old takeover code was moved to account for all possible takeover types
                }
                else if(!strncmp(modeType, "_PASSIVE_", strlen("_PASSIVE_"))) // ICAROUS has handed back control, resume all tasks and Mission
                {
                    printf("UAV %i | passive\n", instanceIndex + 1);
                    // DEBUG STATEMENT - Print what waypoint was last set before handing AMASE back control
                    //fprintf(stderr, "Sending UAV %i to its currentWaypointIndex[instanceIndex] = %lli last waypoint: %lli\n", (instanceIndex + 1), currentWaypointIndex[instanceIndex], icarousClientWaypointLists[instanceIndex][currentWaypointIndex[instanceIndex]]);
                    
                    // If the UAV deviated, it will need to return to the old path before ICAROUS deviated and resume all old tasks
                    deviationMutex[instanceIndex].lock();
                    if(deviationFlags[instanceIndex] == true)
                    {
                        // DEBUG STATEMENT - Print when the UAV has deviated and will need to be redirected to the path
                        //fprintf(stdout, "UAV %i | Deviation flag true, passive recieved!\n", instanceIndex + 1);
                        // SOFT RESET ICAROUS (RESET_SFT)
                        
                        // This will need a soft-reset for ICAROUS to continue
                        softResetFlag[instanceIndex] = true;
                        
                        
                        deviationMutex[instanceIndex].unlock();
                        
                        
                        // Hold the UAV until the new MissionCommand is constructed
                        sem_wait(&softResetSemaphores[instanceIndex]);
                        
                        // Resume tasks after the message is ready
                        for(unsigned int taskIndex = 0; taskIndex < entityTasks[instanceIndex].size(); taskIndex++)
                        {
                            // DEBUG STATEMENT - Used to tell what tasks are being resumed
                            //fprintf(stderr, "UAV %i resuming task #%lli\n", (instanceIndex + 1), entityTasks[instanceIndex][taskIndex]);
                            
                            // Send a message for each task to resume
                            auto resumeTask = std::make_shared<uxas::messages::task::TaskResume>();
                            resumeTask->setTaskID(entityTasks[instanceIndex][taskIndex]);
                            sendSharedLmcpObjectBroadcastMessage(resumeTask);
                        }
                    }
                    // Otherwise the UAV can continue its course and current path
                    // The place the UAV was when this occurs will be marked as the last waypoint to return to on a deviation
                    else
                    {
                        // DEBUG STATEMENT - Print when the UAV has not deviated and can continue its mission
                        //fprintf(stdout, "UAV %i | Deviation flag false, passive recieved!\n", instanceIndex + 1);
                        
                        // If the UAV was able to make the maneuver successfully continue the mission command
                        // heading to the next wp in the list (set it the the first wp and drop the last one at
                        // the last place the UAV was)
                        noDeviationReset[instanceIndex] = true;
                        
                        
                        deviationMutex[instanceIndex].unlock();
                        
                        
                        // Wait for the missionCommand with the updated waypoint to be sent to the UAV
                        sem_wait(&softResetSemaphores[instanceIndex]);
                    }
                    deviationFlags[instanceIndex] = false;
                    icarousTakeoverActive[instanceIndex] = false;
                    
                    
                    // DEBUG STATEMENT - Used to see what the new mission command is composed of
                    //fprintf(stdout, "UAV %i | FirstWaypoint before sending: %lli \n", instanceIndex + 1, missionCommands->getFirstWaypoint());
                    //fprintf(stderr, "SENDING NEW MISSION COMMAND TO UAV %i!!!\n", instanceIndex + 1);
                    //std::cout << missionCommands[instanceIndex]->toString() << std::endl;
                    
                    // Send the new Mission Command to AMASE
                    sendSharedLmcpObjectBroadcastMessage(missionCommands[instanceIndex]);
                    
                    // Inform other parts of the code that a "checkpoint" has been made for the UAV to continue the mission from
                    resumePointSet[instanceIndex] = true;
                }
                
                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else if(!strncmp(tempMessageBuffer, "RPRSP", 5))
            {
                // MESSAGE STRUCTURE - RSRSP,typeST,\n                      - Start of routePlan
                //                     RSRSP,typeWP,lat~,long~,alt~,spd~\n  - A waypoint for a given routePlan
                //                     RSRSP,typeED,\n                      - End of a routePlan
                // DEBUG STATEMENT - Tell what type of message is being processed
                //fprintf(stdout, "RPRSP message received in icarousClientFd %lli!\n", icarousClientFd);
                
                // Get type
                trackingHelper            = strstr(tempMessageBuffer, "type");
                trackingHelper           += 4; //skip past "type"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                char* type                = strncpy(throwaway, trackingHelper, fieldLength);

                // DEBUG STATEMENT - Prints the type of the message
                //fprintf(stdout, "%lli|RPRSP|type|%s\n", icarousClientFd, type);
                
                // Determine the type of the message
                if(!strncmp(type, "ST", 2))
                {
                    // If the routePlan is the first, initialize the overall response for this one
                    if(!isRoutePlanResponseInit[instanceIndex])
                    {
                        auto instanceRoutePlanResponse = std::make_shared<uxas::messages::route::RoutePlanResponse>();
                        instanceRoutePlanResponse->setResponseID(routePlanRequests[instanceIndex][0]->getRequestID());
                        // DEBUG STATEMENT - Print the RequestID of the routePlanResponse
                        //printf("UAV %i | RoutePlanResponse: RequestID = %lli\n", instanceIndex + 1, routePlanRequests[instanceIndex][0]->getRequestID());
                        instanceRoutePlanResponse->setAssociatedTaskID(routePlanRequests[instanceIndex][0]->getAssociatedTaskID());
                        instanceRoutePlanResponse->setVehicleID(routePlanRequests[instanceIndex][0]->getVehicleID());
                        instanceRoutePlanResponse->setOperatingRegion(routePlanRequests[instanceIndex][0]->getOperatingRegion());
                        routePlanResponses[instanceIndex] = instanceRoutePlanResponse;
                        isRoutePlanResponseInit[instanceIndex] = true;
                    }
                    
                    // Create the new routePlan that belongs to the response
                    auto instanceRoutePlan = new uxas::messages::route::RoutePlan();
                    // Each route plan needs the same id as its respecitve constraints
                    instanceRoutePlan->setRouteID(routePlanRequests[instanceIndex][0]->getRouteRequests()[routePlanCounter[instanceIndex]]->getRouteID());
                    // Route cost will be calculated based on the lines that are returned
                    instanceRoutePlan->setRouteCost(0);
                    routePlanCounter[instanceIndex]++;
                    routePlans[instanceIndex] = instanceRoutePlan;
                    
                    // Reset the waypoint id number
                    routePlanWaypointCounter[instanceIndex] = 1;
                }
                else if(!strncmp(type, "WP", 2))
                {
                    // Get waypoint information
                    trackingHelper                = strstr(tempMessageBuffer, "lat");
                    trackingHelper               += 3; //skip past "lat"
                    fieldEnd                      = strchr(trackingHelper, ',');
                    fieldLength                   = fieldEnd - trackingHelper;
                    float latitude                = atof(strncpy(throwaway, trackingHelper, fieldLength));
                    
                    trackingHelper                = strstr(tempMessageBuffer, "long");
                    trackingHelper               += 4; //skip past "long"
                    fieldEnd                      = strchr(trackingHelper, ',');
                    fieldLength                   = fieldEnd - trackingHelper;
                    float longitude               = atof(strncpy(throwaway, trackingHelper, fieldLength));
                    
                    trackingHelper                = strstr(tempMessageBuffer, "alt");
                    trackingHelper               += 3; //skip past "alt"
                    fieldEnd                      = strchr(trackingHelper, ',');
                    fieldLength                   = fieldEnd - trackingHelper;
                    float altitude                = atof(strncpy(throwaway, trackingHelper, fieldLength));
                    
                    trackingHelper                = strstr(tempMessageBuffer, "spd");
                    trackingHelper               += 3; //skip past "spd"
                    fieldEnd                      = strchr(trackingHelper, ',');
                    fieldLength                   = fieldEnd - trackingHelper;
                    float speed                   = atof(strncpy(throwaway, trackingHelper, fieldLength));
                    
                    // If speed if not set, assume the UAVs crusing speed
                    if(speed == 0)
                    {
                        speed = nominalUAVHorizontalSpeed[instanceIndex];
                    }
                    
                    auto waypointToAdd = new afrl::cmasi::Waypoint();
                    waypointToAdd->setNumber(routePlanWaypointCounter[instanceIndex]);
                    waypointToAdd->setNextWaypoint((routePlanWaypointCounter[instanceIndex] + 1));
                    
                    // Calculate the cost of the line that is being added in milliseconds
                    // No need to do calculations on the first waypoint of if there are more then 1024
                    if((routePlanWaypointCounter[instanceIndex] > 1) && (routePlanWaypointCounter[instanceIndex] <= 1024))
                    {
                        // Using Haversine formula to calculate distance between two lat/long points
                        int meanRadiusOfEarth = 6371000;
                        float priorLatitude = routePlans[instanceIndex]->getWaypoints()[routePlanWaypointCounter[instanceIndex] - 2]->getLongitude();
                        float priorLongitude = routePlans[instanceIndex]->getWaypoints()[routePlanWaypointCounter[instanceIndex] - 2]->getLongitude();
                        float lat1Rad = priorLatitude * M_PI / 180;
                        float lat2Rad = latitude * M_PI / 180;
                        float diffLatRad = (latitude - priorLatitude) * M_PI / 180;
                        float diffLongRad = (longitude - priorLongitude) * M_PI / 180;
                        float neededCalculation = sin(diffLatRad / 2) * sin(diffLatRad / 2) + cos(lat1Rad) * cos(lat2Rad) * sin(diffLongRad / 2) * sin(diffLongRad / 2);
                        float distance = meanRadiusOfEarth * (2 * atan2(sqrt(neededCalculation), sqrt(1 - neededCalculation)));
                        
                        int64_t costOfRoute_ms = (distance / speed) * 1000;
                        // DEBUG STATEMENT - Print the cost of the given line segment
                        //printf("UAV %i | Adding Route cost: %lli\n", instanceIndex + 1, costOfRoute_ms);
                        
                        // Add cost of the last line segment
                        routePlans[instanceIndex]->setRouteCost(routePlans[instanceIndex]->getRouteCost() + costOfRoute_ms);
                    }
                    
                    // Add the actual waypoint to the routePlan
                    routePlanWaypointCounter[instanceIndex]++;
                    waypointToAdd->setSpeed(speed);
                    waypointToAdd->setLatitude(latitude);
                    waypointToAdd->setLongitude(longitude);
                    waypointToAdd->setAltitude(altitude);
                    routePlans[instanceIndex]->getWaypoints().push_back(waypointToAdd);
                }
                else if(!strncmp(type, "ED", 2))
                {
                    // Add the route response to the flightplan
                    // Send out the route plan response once all route plans are recieved for the response
                    
                    messageQueueMutex[instanceIndex].lock();
                    // dequeue and send along a WPREQ message to ICAROUS
                    // This is to ensure we do not overflow ICAROUS
                    // TODO - Possibly implement batching of this so that ICAROUS always has a message to do
                    //        This would ensure that latency isn't an issue on this system
                    if(messageQueue[instanceIndex].size() > 0)
                    {
                        dprintf(client_sockfd[instanceIndex], "%s\n", messageQueue[instanceIndex][0].c_str());
                        messageQueue[instanceIndex].erase(messageQueue[instanceIndex].begin());
                    }
                    else
                    {
                        // DEBUG STATEMENT - Print when the message queue for a UAV is finished
                        //printf("Finished Queue for UAV %i\n", instanceIndex + 1);
                    }
                    
                    // If the message queue is empty, then other code should send another message to ICAROUS for WPREQ
                    if(messageQueue[instanceIndex].size() != 0)
                    {
                        waitingForResponse[instanceIndex] = true;
                    }
                    else
                    {
                        waitingForResponse[instanceIndex] = false;
                    }
                    messageQueueMutex[instanceIndex].unlock();
                    
                    // If an invalid route was found (no waypoints, or more then 1024 waypoints), set the cost to -1 (error)
                    if((routePlanWaypointCounter[instanceIndex] == 1) || (routePlanWaypointCounter[instanceIndex] > 1024))
                    {
                        // clear waypoints for invalid routes
                        routePlans[instanceIndex]->getWaypoints().clear();
                        routePlans[instanceIndex]->setRouteCost(-1.0);
                    }
                    else
                    {
                        // DEBUG STATEMENT - Print the last waypoint that was found in a given routePlan
                        //printf("UAV %i | lastWP in routePlan = %lli\n", instanceIndex + 1, routePlans[instanceIndex]->getWaypoints().back()->getNextWaypoint());
                        
                        // Set the last waypoint to point to itself
                        routePlans[instanceIndex]->getWaypoints().back()->setNextWaypoint(routePlanWaypointCounter[instanceIndex] - 1);
                    }
                    
                    // DEBUG STATEMENT - Print the overall cost for this routePlan
                    //printf("Cost for RoutePlan = %lli\n", routePlans[instanceIndex]->getRouteCost());
                    routePlanResponses[instanceIndex]->getRouteResponses().push_back(routePlans[instanceIndex]);
                    
                    // Information statement saying how many routePlans have been done out of the total for this response
                    printf("UAV %i | counter=%i | neededPlans=%i\n", instanceIndex + 1, routePlanCounter[instanceIndex], routePlanRequests[instanceIndex][0]->getRouteRequests().size());
                    
                    // If the routePlan was the last from this request, send the response to UxAS
                    if(routePlanCounter[instanceIndex] == routePlanRequests[instanceIndex][0]->getRouteRequests().size())
                    {
                        sendSharedLmcpObjectBroadcastMessage(routePlanResponses[instanceIndex]);
                        routePlanRequests[instanceIndex].erase(routePlanRequests[instanceIndex].begin());
                        routePlanCounter[instanceIndex] = 0;
                        
                        // Will need to re-initialize a new response after sending this one
                        isRoutePlanResponseInit[instanceIndex] = false;
                    }
                }
                else
                {
                    fprintf(stderr, "UAV %i | Unknown RPRSP message type!\n", instanceIndex + 1);
                }
                
                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else if(!strncmp(tempMessageBuffer, "SETPOS", 6))
            {
                // MESSAGE STRUCTURE - SETPOS,lat~,long~,alt~,\n
                // DEBUG STATEMENT - Tell what type of message is being processed
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


                // DEBUG STATEMENT - Print the contents of the message
                //fprintf(stdout, "%lli|SETPOS|latitude|%f\n", icarousClientFd, latitude);
                //fprintf(stdout, "%lli|SETPOS|longitude|%f\n", icarousClientFd, longitude);
                //fprintf(stdout, "%lli|SETPOS|altitude|%f\n", icarousClientFd, altitude);

                // Create a new vehicle action command and send the UAV to the given position
                auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
                vehicleActionCommand->setVehicleID(instanceIndex + 1);

                // Loiter at the given position until another command is recieved
                auto loiterAction = new afrl::cmasi::LoiterAction;
                auto location3d = new afrl::cmasi::Location3D;
                location3d->setLatitude(latitude);
                location3d->setLongitude(longitude);
                location3d->setAltitude(altitude);
                loiterAction->setLocation(location3d);
                loiterAction->setDuration(-1); // Loiter at this location until told otherwise
                

                vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
                sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);


                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }
            else if(!strncmp(tempMessageBuffer, "SETVEL", 6))
            {
                // MESSAGE STRUCTURE - SETVEL,north~,east~,down~,\n
                // DEBUG STATEMENT - Tell what type of message is being processed
                //fprintf(stdout, "SETVEL message received in icarousClientFd %lli!\n", icarousClientFd);
                
                // Get north
                trackingHelper            = strstr(tempMessageBuffer, "north");
                trackingHelper           += 5; //skip past "north"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float north     = atof(strncpy(throwaway, trackingHelper, fieldLength));

                // Get east
                trackingHelper            = strstr(tempMessageBuffer, "east");
                trackingHelper           += 4; //skip past "east"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float east     = atof(strncpy(throwaway, trackingHelper, fieldLength));

                // Get down
                trackingHelper            = strstr(tempMessageBuffer, "down");
                trackingHelper           += 4; //skip past "down"
                fieldEnd                  = strchr(trackingHelper, ',');
                fieldLength               = fieldEnd - trackingHelper;
                float down     = atof(strncpy(throwaway, trackingHelper, fieldLength));
                
                
                // DEBUG STATEMENT - Print the contents of the message
                //fprintf(stdout, "%lli|SETVEL|north|%f\n", icarousClientFd, north);
                //fprintf(stdout, "%lli|SETVEL|east|%f\n", icarousClientFd, east);
                //fprintf(stdout, "%lli|SETVEL|down|%f\n", icarousClientFd, down);

                
                //fprintf(stdout, "Starting creationg of VehicleActionCommand message\n");                
                auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
                vehicleActionCommand->setVehicleID(instanceIndex + 1);
                
                // loiter at this location
                if((north == 0) && (east == 0))
                {
                    auto loiterAction =  new afrl::cmasi::LoiterAction;
                    auto location3d = new afrl::cmasi::Location3D;
                    currentInformationMutexes[instanceIndex].lock();
                    location3d->setLatitude(currentInformation[instanceIndex][1]);
                    location3d->setLongitude(currentInformation[instanceIndex][2]);
                    location3d->setAltitude(down + currentInformation[instanceIndex][3]);
                    currentInformationMutexes[instanceIndex].unlock();
                    loiterAction->setLocation(location3d);
                    loiterAction->setDuration(-1); // Loiter at this location until told otherwise
                    
                    vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
                }
                // otherwise set a FlightDirectorAction to move in a certain direction
                else
                {
                    auto flightDirectorAction = new afrl::cmasi::FlightDirectorAction;
                    
                    // Calculate the actual speed and heading of where the UAV should be going
                    double actualSpeed = sqrt(pow(north,2)+pow(east,2));
                    double heading = acos(north / sqrt(pow(north, 2) + pow(east, 2))) * 180 / M_PI;
                    
                    // Convert the heading to 0-360 as needed
                    if(east < 0)
                    {
                        heading = 360 - heading;
                    }
                    
                    // Add the information to the message
                    flightDirectorAction->setSpeed(actualSpeed);
                    flightDirectorAction->setHeading(heading);
                    flightDirectorAction->setClimbRate(-down);
                    vehicleActionCommand->getVehicleActionList().push_back(flightDirectorAction);
                }
                
                // DEBUG STATEMENT - Print the newly constructed message before sending it
                //std::cout << vehicleActionCommand->getVehicleActionList().front()->toString() << std::endl;;
                
                sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);
                
                // Cut off the processed part of tempMessageBuffer using pointer arithmetic
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
            }           
            else
            {
                fprintf(stderr,"Error, unknown message type! Skipping to next message!\n");
                fieldEnd = strchr(tempMessageBuffer, '\n');
                tempMessageBuffer = fieldEnd;
                tempMessageBuffer++;
                //exit(EXIT_FAILURE);
            }
            
            //END OF MESSAGE PROCESSING FROM ICAROUS
        }
    }
}



// This function is performed to cleanly terminate the service
bool IcarousCommunicationService::terminate()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    // Rejoin all threads on a termination
    for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
    {
        icarousID[i].join();
    }
    
    return (true);
}



// Listen for defined messages and relay them to the needed ICAROUS instance they belong to
bool IcarousCommunicationService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    /*
    // Template for added new message parsing
    if(<namespace>::<namespace>::is<type>(receivedLmcpMessage->m_object))
    {
        auto ptr_<type> = std::shared_ptr<<namespace>::<namespace>::<type>((<namespace>::<namespace>::<type>*)receivedLmcpMessage->m_object->clone());
        // Parsing code
        ptr_<type>->getInformation();
        
        // Sending ICAROUS a Dummy Command message
        dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,\n",
            "Dummy Command");
    }// End of Template
    else
    */
    
    // Parse the AirVehicleConfiguration for the UAVs nominal speeds
    if(afrl::cmasi::isAirVehicleConfiguration(receivedLmcpMessage->m_object))
    {
        auto ptr_AirVehicleConfiguration = std::shared_ptr<afrl::cmasi::AirVehicleConfiguration>((afrl::cmasi::AirVehicleConfiguration*)receivedLmcpMessage->m_object->clone());
        auto vehicleID = ptr_AirVehicleConfiguration->getID();
        if(vehicleID <= ICAROUS_CONNECTIONS)
        {
            auto ptr_NominalFlightProfile = ptr_AirVehicleConfiguration->getNominalFlightProfile();
            nominalUAVHorizontalSpeed[vehicleID - 1] = ptr_NominalFlightProfile->getAirspeed();
            nominalUAVVerticleSpeed[vehicleID - 1] = ptr_NominalFlightProfile->getVerticalSpeed();
        }
    }// End of AirVehicleConfiguration
    // Process a RoutePlanRequest
    // If -1 do not use ICAROUS route planners
    else if(uxas::messages::route::isRoutePlanRequest(receivedLmcpMessage->m_object) && (ICAROUS_ROUTEPLANNER > -1))
    {
        auto ptr_RoutePlanRequest = std::shared_ptr<uxas::messages::route::RoutePlanRequest>((uxas::messages::route::RoutePlanRequest*)receivedLmcpMessage->m_object->clone());
        auto vehicleID = ptr_RoutePlanRequest->getVehicleID();
        if(vehicleID <= ICAROUS_CONNECTIONS)
        {
            // Let UxAS Visibility planner handle the costs of each request
            if(!ptr_RoutePlanRequest->getIsCostOnlyRequest())
            {
                auto ptr_VectorRouteConstraints = ptr_RoutePlanRequest->getRouteRequests();
                routePlanRequests[vehicleID - 1].push_back(ptr_RoutePlanRequest);
                std::string wpreqType = "";
                
                // Determine the planner to use
                switch(ICAROUS_ROUTEPLANNER)
                {
                    case 0: // GRID planner
                        wpreqType = "GRID";
                        break;
                    case 1: // ASTAR planner
                        wpreqType = "ASTAR";
                        break;
                    case 2: // RRT planner
                        wpreqType = "RRT";
                        break;
                    case 3: // SPLINE
                        wpreqType = "SPLINE";
                        break;
                }
                
                // For each routePlanConstraint, construct a request to ICAROUS
                for(unsigned int i = 0; i < ptr_VectorRouteConstraints.size(); i++)
                {
                    auto startLocation = ptr_VectorRouteConstraints[i]->getStartLocation();
                    auto endLocation = ptr_VectorRouteConstraints[i]->getEndLocation();
                    // TODO - altitudes of some route plans are being given at 0, this is an issue with the route requests being incorrect (Unsure how to fix). For now, if they are 0, they are hard-codded
                    if(endLocation->getAltitude() == 0)
                    {
                        endLocation->setAltitude(400);
                        startLocation->setAltitude(400);
                        //startLocation->getAltitude());
                    }
                    // TODO - End heading needs to be accounted for (currently ICAROUS cannot do that)
                    // Save into request vector
                    // (This is the EXACT request message that needs to be sent without the newline)
                    // (need to add \n at the end when sending)
                    std::string messageToAdd = "WPREQ,type"
                                               + wpreqType
                                               + ",slat"
                                               + std::to_string(startLocation->getLatitude())
                                               + ",slong"
                                               + std::to_string(startLocation->getLongitude())
                                               + ",salt"
                                               + std::to_string(startLocation->getAltitude())
                                               + ",elat"
                                               + std::to_string(endLocation->getLatitude())
                                               + ",elong"
                                               + std::to_string(endLocation->getLongitude())
                                               + ",ealt"
                                               + std::to_string(endLocation->getAltitude())
                                               + ",track"
                                               + std::to_string(ptr_VectorRouteConstraints[i]->getStartHeading())
                                               + ",vh"
                                               + std::to_string(nominalUAVHorizontalSpeed[vehicleID - 1])
                                               + ",vv"
                                               + std::to_string(nominalUAVVerticleSpeed[vehicleID - 1])
                                               + ",";

                    // If this is the first request, send it; otherwise, add it to the request queue
                    messageQueueMutex[vehicleID - 1].lock();
                    messageQueue[vehicleID - 1].push_back(messageToAdd);
                    if(!waitingForResponse[vehicleID - 1])
                    {
                        dprintf(client_sockfd[vehicleID - 1], "%s\n", messageQueue[vehicleID - 1][0].c_str());
                        messageQueue[vehicleID - 1].erase(messageQueue[vehicleID - 1].begin());
                        waitingForResponse[vehicleID - 1] = true;
                    }
                    messageQueueMutex[vehicleID - 1].unlock();
                }
            }
        }
    }// End of RoutePlanRequest
    // Process a MissionCommand message
    else if (afrl::cmasi::isMissionCommand(receivedLmcpMessage->m_object))
    {
        // Copy the message pointer to shorten access length
        auto ptr_MissionCommand = std::shared_ptr<afrl::cmasi::MissionCommand>((afrl::cmasi::MissionCommand*)receivedLmcpMessage->m_object->clone());
        
        // Grab the vehicles's ID to use as an index + 1
        // (so when using it as an index, it should be [vehicleID - 1])
        auto vehicleID = ptr_MissionCommand->getVehicleID();
        if(vehicleID <= ICAROUS_CONNECTIONS)
        {
            //std::cout << "Vehicle ID is " << vehicleID << "\n";
            
            // Check that the vehicle has not already recieved its waypoints
            if (!has_gotten_waypoints[vehicleID - 1])
            {
                // Set the variable to ensure we only send one vehicle one MissionCommand
                has_gotten_waypoints[vehicleID - 1] = true;
                
                // Set up variable to be used
                int waypointIndex = (ptr_MissionCommand->getFirstWaypoint() - 1);
                int totalNumberOfWaypoints = 0;
                int nextWaypoint = ptr_MissionCommand->getWaypointList()[waypointIndex]->getNextWaypoint();
                int priorWPIndex = -1;
                
                //Resize the vectors to the size of the waypoint lists
                icarousClientWaypointLists[vehicleID - 1].resize(ptr_MissionCommand->getWaypointList().size());
                headingLists[vehicleID - 1].resize(ptr_MissionCommand->getWaypointList().size());
                
                // Save the mission command to be used to send new ones later
                missionCommands[vehicleID - 1] = ptr_MissionCommand;
                
                // Save the original starting waypoint
                originalStartingWaypoint[vehicleID - 1] = ptr_MissionCommand->getFirstWaypoint();

                // Soft Reset ICAROUS to reset the waypoints it was using if a path planner was specified
                // Values are ignored due to not reaching a waypoint
                dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,lat%f,long%f,alt%f,\n",
                    "RESET_SFT",
                    0.0,
                    0.0,
                    0.0);

                // For each waypoint in the mission command, send each as its own message to ICAROUS
                // The last waypoint's next value will be equal to itself (This indicates the end)
                while(nextWaypoint != (ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber()))
                {
                    totalNumberOfWaypoints++;
                    
                    // DEBUG STATEMENT - Print what waypoint index indicates is the next waypoint and what waypoint is being sent
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

                    if(totalNumberOfWaypoints > 1)
                    {
                        // Prior waypoint
                        float lat1  = ptr_MissionCommand->getWaypointList()[priorWPIndex]->getLatitude();
                        float long1 = ptr_MissionCommand->getWaypointList()[priorWPIndex]->getLongitude();

                        // Current Waypoint
                        float lat2  = ptr_MissionCommand->getWaypointList()[waypointIndex]->getLatitude();
                        float long2 = ptr_MissionCommand->getWaypointList()[waypointIndex]->getLongitude();

                        // Calculate the bearing for the segment
                        headingLists[vehicleID - 1][totalNumberOfWaypoints - 2] = fmod(360 + (atan2(
                            cos(lat2)*sin(long2-long1),
                            cos(lat1)*sin(lat2)-sin(lat1)*cos(lat2)*cos(long2-long1)) * 180/M_PI), 360);
                        /*
                        // DEBUG STATEMENT - Print the headings for each segment that a UAV must follow to stay on the path
                        fprintf(stdout, "UAV %lli | Path %i | Heading %f\n",
                            vehicleID,
                            totalNumberOfWaypoints - 1,
                            headingLists[vehicleID - 1][totalNumberOfWaypoints - 2]);
                        printf("\tLat1 %f | Long1 %f\n\tLat2 %f | Long2 %f\n", lat1, long1, lat2, long2);
                        */
                    }

                    // Need to convert numbers to the indexes
                    // Then store the lat long and alt of each waypoint
                    // This is to put them all into an ordered list for easy access when getting a GOTOWAYPOINT command
                    icarousClientWaypointLists[vehicleID - 1][totalNumberOfWaypoints - 1] = ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber();
                    // Also save this list into a vector
                    newWaypointLists[vehicleID - 1].push_back(ptr_MissionCommand->getWaypointList()[waypointIndex]);
                    
                    // DEBUG STATEMENT - Print how the waypoints were saved
                    //fprintf(stderr, "UAV %lli | Stored index %i as %lli\n", vehicleID, (totalNumberOfWaypoints - 1), ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber());
                    
                    // Set the index of the next waypoint
                    priorWPIndex = waypointIndex;
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
                
                // Create a list of headings the UAV must follow to not deviate from the path
                if(totalNumberOfWaypoints > 1)
                {
                    // Prior waypoint
                    float lat1  = ptr_MissionCommand->getWaypointList()[priorWPIndex]->getLatitude();
                    float long1 = ptr_MissionCommand->getWaypointList()[priorWPIndex]->getLongitude();

                    // Current Waypoint
                    float lat2  = ptr_MissionCommand->getWaypointList()[waypointIndex]->getLatitude();
                    float long2 = ptr_MissionCommand->getWaypointList()[waypointIndex]->getLongitude();

                    // Calculate the bearing for the segment
                    headingLists[vehicleID - 1][totalNumberOfWaypoints - 2] = fmod(360 + (atan2(
                        cos(lat2)*sin(long2-long1),
                        cos(lat1)*sin(lat2)-sin(lat1)*cos(lat2)*cos(long2-long1)) * 180/M_PI), 360);
                }
                
                icarousClientWaypointLists[vehicleID - 1][totalNumberOfWaypoints - 1] = ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber();
                newWaypointLists[vehicleID - 1].push_back(ptr_MissionCommand->getWaypointList()[waypointIndex]);
                //fprintf(stderr, "UAV %lli | Stored index %i as %lli\n", vehicleID, (totalNumberOfWaypoints - 1), ptr_MissionCommand->getWaypointList()[waypointIndex]->getNumber());
                
                //Send a message to ICAROUS telling it to start the mission
                dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,\n",
                "START_MISSION");
            }
        }
    }// End of MissionCommand
    // Process a KeepInZone
    else if(afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
    {
        //fprintf(stdout, "Keep In Geofence\n");
        
        // Copy the message pointer to shorten access length
        auto ptr_Zone = std::shared_ptr<afrl::cmasi::KeepInZone>((afrl::cmasi::KeepInZone*)receivedLmcpMessage->m_object->clone());
        
        // Get the number of vertices of the polygon zone
        int lengthOfZone = ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints().size();
        //fprintf(stdout, "Length of KeepIn:%i\n", lengthOfZone);


        // Broadcast this message to all ICAROUS instances
        for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
        {
            // Send each zone's vertices one at a time
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
            dprintf(client_sockfd[i], "COMND,type%s,id%lli.0,\n",
            "GEOFN_SEND",
            ptr_Zone->getZoneID());
        }
    }// End of KeepInZone
    // Process a KeepOutZone
    else if(afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
    {
        //fprintf(stdout, "Keep Out Geofence\n");
        
        // Copy the message pointer to shorten access length
        auto ptr_Zone = std::shared_ptr<afrl::cmasi::KeepOutZone>((afrl::cmasi::KeepOutZone*)receivedLmcpMessage->m_object->clone());
        
        // Get the number of vertices of the polygon zone
        int lengthOfZone = ((afrl::cmasi::Polygon*)ptr_Zone->getBoundary())->getBoundaryPoints().size();
        //fprintf(stdout, "Length of KeepOut:%i\n", lengthOfZone);


        // Broadcast this message to all ICAROUS instances
        for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
        {
            // Send each zone's vertices one at a time
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
            dprintf(client_sockfd[i], "COMND,type%s,id%lli.0,\n",//,id%lld.0,\n",
            "GEOFN_SEND",
            ptr_Zone->getZoneID());//,
            //ptr_Zone->getZoneID());
        }
    }// End of KeepOutZone Check
    // Process an AirVehicleState from OpenAMASE
    else if(afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object))
    {
        // Copy the message pointer to shorten access length
        auto ptr_AirVehicleState = std::shared_ptr<afrl::cmasi::AirVehicleState>((afrl::cmasi::AirVehicleState *)receivedLmcpMessage->m_object->clone());
        int vehicleID = ptr_AirVehicleState->getID();
        if(vehicleID <= ICAROUS_CONNECTIONS)
        {
            //fprintf(stdout, "UAV %i | recieved usable AirVehicleState\n", vehicleID);

            // Save the current information of the UAV
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
            
            // TODO - un-hardcode the number of sats
            // Get the current tasks and update the list (Only when ICAROUS does not have control)
            if(deviationFlags[vehicleID - 1] == false)
            {
                // Save the current tasks the UAV was doing before a takeover
                entityTasks[vehicleID - 1] = ptr_AirVehicleState->getAssociatedTasks();
                
                // Send the position of the UAV to ICAROUS every time it updates from AMASE
                positionBeforeTakeover[vehicleID - 1][0] = ptr_AirVehicleState->getHeading();
                positionBeforeTakeover[vehicleID - 1][1] = ptr_AirVehicleState->getLocation()->getLatitude();
                positionBeforeTakeover[vehicleID - 1][2] = ptr_AirVehicleState->getLocation()->getLongitude();
                positionBeforeTakeover[vehicleID - 1][3] = ptr_AirVehicleState->getLocation()->getAltitude();
                // Updates the current waypoint to the waypoint the UAV is currently doing
                // Also saves this waypoint to be compared to the next to ensure that a change of waypoints is seen
                if(isLastWaypointInitialized[vehicleID - 1])
                {
                    // For each waypoint that it is past, send a waypoint reached message
                    //fprintf(stderr, "UAV %i | currentWP = %lli | otherWP = %lli\n", vehicleID, currentWaypointIndex[vehicleID - 1], (ptr_AirVehicleState->getCurrentWaypoint() - originalStartingWaypoint[vehicleID - 1]));
                    while(currentWaypointIndex[vehicleID - 1] < (ptr_AirVehicleState->getCurrentWaypoint() - originalStartingWaypoint[vehicleID - 1]))
                    {
                        // If a waypoint was reached, a new resume point can be set
                        resumePointSet[vehicleID - 1] = false;
                        dprintf(client_sockfd[vehicleID - 1], "WPRCH,id%lli.0,\n",
                            currentWaypointIndex[vehicleID - 1]);

                        currentWaypointIndex[vehicleID - 1]++;
                        
                        // Remove a waypoint unless it is the first or we have yet to reach it due to a takeover
                        if(truncateWaypoint[vehicleID - 1] == true)
                        {
                            newWaypointLists[vehicleID - 1].erase(newWaypointLists[vehicleID - 1].begin());
                        }else{
                            truncateWaypoint[vehicleID - 1] = true;
                        }
                        
                        // As long as the waypoint is not the last waypoint, increase it
                        if(lastWaypoint[vehicleID - 1] != ptr_AirVehicleState->getCurrentWaypoint())
                        {
                            lastWaypoint[vehicleID - 1]++;
                        }
                        
                        // Wait 100 milliseconds to allow ICAROUS to process a waypoint recieved message
                        sleep(0.1);
                    }
                }
                else
                {
                    // On the first waypoint, initialize all values
                    isLastWaypointInitialized[vehicleID - 1] = true;
                    lastWaypoint[vehicleID - 1] = 0;
                    currentWaypointIndex[vehicleID - 1] = 0;
                }
            }

            // TODO - add XML option to make distance from a line configurable and default to 500m
            // Check for deviations from the mission that are > 500 meters
            if(icarousTakeoverActive[vehicleID - 1] == true){
                //This is erroring, this means newWaypointLists isn't initialized on the first AirVehicleState, Add a check for this
                double lat1 = newWaypointLists[vehicleID - 1][0]->getLatitude();
                double lat2 = newWaypointLists[vehicleID - 1][1]->getLatitude();
                double long1 = newWaypointLists[vehicleID - 1][0]->getLongitude();
                double long2 = newWaypointLists[vehicleID - 1][1]->getLongitude();            
                double pointToCheckLat = currentInformation[vehicleID - 1][1];
                double pointToCheckLong = currentInformation[vehicleID - 1][2];
                
                double bearing1 = atan2(sin(pointToCheckLong - long1) * cos(pointToCheckLat), 
                                        cos(lat1) * sin(pointToCheckLat) - sin(lat1) * cos(pointToCheckLat) * cos(pointToCheckLat - lat1)) * 180 / M_PI;
                bearing1 = 360 - (fmod((bearing1 + 360), 360));
                
                double bearing2 = atan2(sin(long2 - long1) * cos(lat2),
                                        cos(lat1) * sin(lat2) - sin(lat1) * cos(lat2) * cos(lat2 - lat1)) * 180 / M_PI;
                bearing2 = 360 - (fmod((bearing2 + 360),360));

                double lat1InRad = lat1 * M_PI / 180;
                double pointToCheckLatInRad = pointToCheckLat * M_PI / 180;
                double deltaLong = (pointToCheckLong - long1) * M_PI / 180;

                double distanceAC = acos(sin(lat1InRad) * sin(pointToCheckLatInRad)+cos(lat1InRad)*cos(pointToCheckLatInRad)*cos(deltaLong)) * 6371;  
                double min_distance = fabs(asin(sin(distanceAC/6371)*sin((bearing1 * M_PI / 180)-(bearing2 * M_PI / 180))) * 6371);
                min_distance = min_distance * 1000; // Need to convert km to to m
                deviationMutex[vehicleID - 1].lock();
                //fprintf(stderr, "UAV %i | LINE_VOLUME = %i | min_distance = %f\n", vehicleID, LINE_VOLUME, min_distance);
                if((min_distance > LINE_VOLUME) && (deviationFlags[vehicleID - 1] == false))
                {
                    //fprintf(stderr, "!!!WARNING, UAV %i has deviated from path!!!\n", vehicleID);
                    // Set this flag to true when a deviation of more then 5 degrees occurs
                    deviationFlags[vehicleID - 1] = true;
                    
                    // If a takeover that deviates from the path has started, waypoints should stop being truncated
                    truncateWaypoint[vehicleID - 1] = false;
                    
                    // Pause all current tasks the UAV is doing
                    for(unsigned int taskIndex = 0; taskIndex < entityTasks[vehicleID - 1].size(); taskIndex++)
                    {
                        // DEBUG STATEMENT - Print what tasks were paused
                        //fprintf(stderr, "UAV %i pausing task #%lli\n", (instanceIndex + 1), entityTasks[instanceIndex][taskIndex]);
                        // Pause the task by sending a message to AMASE
                        auto pauseTask = std::make_shared<uxas::messages::task::TaskPause>();
                        pauseTask->setTaskID(entityTasks[vehicleID - 1][taskIndex]);
                        sendSharedLmcpObjectBroadcastMessage(pauseTask);
                    }
                }
                deviationMutex[vehicleID - 1].unlock();
            }
            
            // TODO - This needs re-worked to account for pitch angle
            //        (For now, this works when planning is only done in 2D space)
            
            double uHeading = fmod((ptr_AirVehicleState->getHeading() + 360), 360.0);
            double vHeading = fmod((uHeading + 90), 360.0);
            double uNorth;
            double vNorth;
            double uEast;
            double vEast;
            double wDown = ptr_AirVehicleState->getW();
            
            uNorth = ptr_AirVehicleState->getU() * cos(uHeading*M_PI/180);
            uEast = ptr_AirVehicleState->getU() * sin(uHeading*M_PI/180);
            
            vNorth = ptr_AirVehicleState->getV() * cos(vHeading*M_PI/180);
            vEast = ptr_AirVehicleState->getV() * sin(vHeading*M_PI/180);
            
            
            double northTotal = uNorth + vNorth;
            double eastTotal = uEast + vEast;
            double downTotal = wDown;
            
            // Inform ICAROUS of its position information using North-East-Down format
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

            // Send the attitude of the UAV (roll,pitch,yaw) every time it updates from AMASE
            dprintf(client_sockfd[vehicleID - 1], "ATTUD,roll%f,pitch%f,yaw%f,\n",
                ptr_AirVehicleState->getRoll(),
                ptr_AirVehicleState->getPitch(),
                0.0);// TODO - find a way to actually get Yaw (no way currently from AirVehicleState)


            // For all other ICAROUS connections, send the UAV as a traffic obsticle to avoid
            for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
            {
                // Do not send this information to itself
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

            // If a soft reset was requested, initiate it only if it was not already done
            // It will allow a new one to be created if the UAV goes further then before the takeover
            if((softResetFlag[vehicleID - 1] == true) && (resumePointSet[vehicleID - 1] == false))
            {

                
                //int indexOfWaypointToReplace = icarousClientWaypointLists[vehicleID - 1][currentWaypointIndex[vehicleID - 1] - 1] - 1;
                
                //fprintf(stdout, "UAV %i | Replacing waypoint %i at index %lli\n", vehicleID, indexOfWaypointToReplace, currentWaypointIndex[vehicleID - 1] - 1);
                
                // Save the new point AMASE should start at
                
                // Calculate the point projected onto the line made by the last waypoint done and the current waypoint
                // (Calculate the ortogonal projection of the UAV onto the line it should be following)
                // This is expanded out in such a way that it would be easier to read
                double lat1 = newWaypointLists[vehicleID - 1][0]->getLatitude();
                double lat2 = newWaypointLists[vehicleID - 1][1]->getLatitude();
                double long1 = newWaypointLists[vehicleID - 1][0]->getLongitude();
                double long2 = newWaypointLists[vehicleID - 1][1]->getLongitude();
                double positionLat = positionBeforeTakeover[vehicleID - 1][1];
                double positionLong = positionBeforeTakeover[vehicleID - 1][2];
                
                double e1x = lat2 - lat1;
                double e1y = long2 - long1;
                double e2x = positionLat - lat1;
                double e2y = positionLong - long1;
                double eDotProduct = e1x * e2x + e1y * e2y;
                double e1DotProduct = e1x * e1x + e1y * e1y;
                double len2 = pow(e1x, 2) + pow(e1y, 2);
                double newPointLat = (lat1 + (eDotProduct * e1x) / len2);
                double newPointLong = (long1 + (eDotProduct * e1y) / len2);
                
                // If both the UAVs current position and the waypoint being checked are the exact same, don't change the waypoint
                // Also check if the new point falls within the two points
                if((lat1 != lat2) && (long1 != long2) && ((eDotProduct > 0) && (eDotProduct < e1DotProduct)))
                {
                    // Tell ICAROUS to initiate a soft-reset
                    dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,lat%f,long%f,alt%f,\n",
                        "RESET_SFT",
                        newPointLat,
                        newPointLong,
                        positionBeforeTakeover[vehicleID - 1][3]);
                    
                    // Adjust the first points to be these new points
                    newWaypointLists[vehicleID - 1][0]->setLatitude(
                        newPointLat);
                    
                    newWaypointLists[vehicleID - 1][0]->setLongitude(
                        newPointLong);
                    
                    newWaypointLists[vehicleID - 1][0]->setAltitude(
                        positionBeforeTakeover[vehicleID - 1][3]);
                }
                else if(eDotProduct < e1DotProduct)
                {
                    dprintf(client_sockfd[vehicleID - 1], "WPRCH,id%lli.0,\n",
                        currentWaypointIndex[vehicleID - 1]);
                    currentWaypointIndex[vehicleID - 1]++;
                    newWaypointLists[vehicleID - 1].erase(newWaypointLists[vehicleID - 1].begin());
                    
                    // Tell ICAROUS to initiate a soft-reset
                    dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,lat%f,long%f,alt%f,\n",
                        "RESET_SFT",
                        newWaypointLists[vehicleID - 1][0]->getLatitude(),
                        newWaypointLists[vehicleID - 1][0]->getLongitude(),
                        newWaypointLists[vehicleID - 1][0]->getAltitude());
                }
                else
                {
                    dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,lat%f,long%f,alt%f,\n",
                        "RESET_SFT",
                        newWaypointLists[vehicleID - 1][0]->getLatitude(),
                        newWaypointLists[vehicleID - 1][0]->getLongitude(),
                        newWaypointLists[vehicleID - 1][0]->getAltitude());
                }
                
                // Set this new point as the first point
                missionCommands[vehicleID - 1]->setFirstWaypoint(newWaypointLists[vehicleID - 1][0]->getNumber());
                
                // Reset the commandID to have the UAV replace the old mission command
                missionCommands[vehicleID - 1]->setCommandID(0);
                
                // Remove all old waypoints
                missionCommands[vehicleID - 1]->getWaypointList().clear();
                
                // Add all new waypoints plus a copy of the first because the first one is always ignored
                missionCommands[vehicleID - 1]->getWaypointList().push_back(newWaypointLists[vehicleID - 1][0]);
                for(unsigned int i = 0; i < newWaypointLists[vehicleID - 1].size(); i++)
                {
                    // DEBUG STATEMENT - Print what waypoints are being set
                    //fprintf(stderr, "UAV %i | Setting waypointList at %i to %lli\n", vehicleID, i, newWaypointLists[vehicleID - 1][i]->getNumber());
                    missionCommands[vehicleID - 1]->getWaypointList().push_back(newWaypointLists[vehicleID - 1][i]);
                }
                
                // The mission command was created, now send it along
                
                // Re-send the last waypoint done due to moving back one waypoint
                if(lastWaypoint[vehicleID - 1] > 0)
                {
                    lastWaypoint[vehicleID - 1]--;
                }
                
                if(currentWaypointIndex[vehicleID - 1] > 0)
                {
                    currentWaypointIndex[vehicleID - 1]--;
                }
                
                softResetFlag[vehicleID - 1] = false;
                sem_post(&softResetSemaphores[vehicleID - 1]);
            }
            // If it was already set, just resend the old mission command
            else if((softResetFlag[vehicleID - 1] == true) && (resumePointSet[vehicleID - 1] == true))
            {   
                // Otherwise if we already have a waypoint set, continue the original mission
                softResetFlag[vehicleID - 1] = false;
                sem_post(&softResetSemaphores[vehicleID - 1]);
            }
            // If no deviation occured, update the last point that ICAROUS handed back control
            else if(noDeviationReset[vehicleID - 1] == true)
            {
                // Calculate the point projected onto the line made by the last waypoint done and the current waypoint
                // (Calculate the ortogonal projection of the UAV onto the line it should be following)
                // This is expanded out in such a way that it would be easier to read
                double lat1 = newWaypointLists[vehicleID - 1][0]->getLatitude();
                double lat2 = newWaypointLists[vehicleID - 1][1]->getLatitude();
                double long1 = newWaypointLists[vehicleID - 1][0]->getLongitude();
                double long2 = newWaypointLists[vehicleID - 1][1]->getLongitude();
                double positionLat = currentInformation[vehicleID - 1][1];
                double positionLong = currentInformation[vehicleID - 1][2];

                double e1x = lat2 - lat1;
                double e1y = long2 - long1;
                double e2x = positionLat - lat1;
                double e2y = positionLong - long1;
                double eDotProduct = e1x * e2x + e1y * e2y;
                double e1DotProduct = e1x * e1x + e1y * e1y;
                double len2 = pow(e1x, 2) + pow(e1y, 2);
                double newPointLat = (lat1 + (eDotProduct * e1x) / len2);
                double newPointLong = (long1 + (eDotProduct * e1y) / len2);

                // If both the UAVs current position and the waypoint being checked are the exact same, don't change the waypoint
                // Also check if the new point falls within the two points
                if((lat1 != lat2) && (long1 != long2) && ((eDotProduct > 0) && (eDotProduct < e1DotProduct)))
                {
                    // Tell ICAROUS to initiate a soft-reset
                    dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,lat%f,long%f,alt%f,\n",
                        "RESET_SFT",
                        newPointLat,
                        newPointLong,
                        currentInformation[vehicleID - 1][3]);

                    // Adjust the first points to be these new points
                    newWaypointLists[vehicleID - 1][0]->setLatitude(
                        newPointLat);
                    
                    newWaypointLists[vehicleID - 1][0]->setLongitude(
                        newPointLong);
                    
                    newWaypointLists[vehicleID - 1][0]->setAltitude(
                        currentInformation[vehicleID - 1][3]);
                }
                else if(eDotProduct < e1DotProduct)
                {
                    dprintf(client_sockfd[vehicleID - 1], "WPRCH,id%lli.0,\n",
                        currentWaypointIndex[vehicleID - 1]);
                    currentWaypointIndex[vehicleID - 1]++;
                    newWaypointLists[vehicleID - 1].erase(newWaypointLists[vehicleID - 1].begin());
                    
                    // Tell ICAROUS to initiate a soft-reset
                    dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,lat%f,long%f,alt%f,\n",
                        "RESET_SFT",
                        newWaypointLists[vehicleID - 1][0]->getLatitude(),
                        newWaypointLists[vehicleID - 1][0]->getLongitude(),
                        newWaypointLists[vehicleID - 1][0]->getAltitude());
                }
                else
                {
                    // Tell ICAROUS to initiate a soft-reset
                    dprintf(client_sockfd[vehicleID - 1], "COMND,type%s,lat%f,long%f,alt%f,\n",
                        "RESET_SFT",
                        newWaypointLists[vehicleID - 1][0]->getLatitude(),
                        newWaypointLists[vehicleID - 1][0]->getLongitude(),
                        newWaypointLists[vehicleID - 1][0]->getAltitude());
                }
                
                // Set this new point as the first point
                missionCommands[vehicleID - 1]->setFirstWaypoint(newWaypointLists[vehicleID - 1][1]->getNumber());
                
                // Reset the commandID to have the UAV replace the old mission command
                missionCommands[vehicleID - 1]->setCommandID(0);
                
                // Remove all old waypoints
                missionCommands[vehicleID - 1]->getWaypointList().clear();
                
                // Add all new waypoints plus a copy of the first because the first one is always ignored
                missionCommands[vehicleID - 1]->getWaypointList().push_back(newWaypointLists[vehicleID - 1][0]);
                for(unsigned int i = 0; i < newWaypointLists[vehicleID - 1].size(); i++)
                {
                    // DEBUG STATEMENT - Print what waypoints are being set
                    //fprintf(stderr, "UAV %i | Setting waypointList at %i to %lli\n", vehicleID, i, newWaypointLists[vehicleID - 1][i]->getNumber());
                    missionCommands[vehicleID - 1]->getWaypointList().push_back(newWaypointLists[vehicleID - 1][i]);
                }
                
                noDeviationReset[vehicleID - 1] = false;
                sem_post(&softResetSemaphores[vehicleID - 1]);
            }
        }
        // Intruder vehicles still need to report their location to ICAROUS instances
        else
        {
            // TODO - This needs re-worked to account for pitch angle
            //        (For now, this works when planning is only done in 2D space)
            
            double uHeading = fmod((ptr_AirVehicleState->getHeading() + 360), 360.0);
            double vHeading = fmod((uHeading + 90), 360.0);
            double uNorth;
            double vNorth;
            double uEast;
            double vEast;
            double wDown = ptr_AirVehicleState->getW();
            
            uNorth = ptr_AirVehicleState->getU() * cos(uHeading*M_PI/180);
            uEast = ptr_AirVehicleState->getU() * sin(uHeading*M_PI/180);
            
            vNorth = ptr_AirVehicleState->getV() * cos(vHeading*M_PI/180);
            vEast = ptr_AirVehicleState->getV() * sin(vHeading*M_PI/180);
            
            
            double northTotal = uNorth + vNorth;
            double eastTotal = uEast + vEast;
            double downTotal = wDown;
            
            // For all other ICAROUS connections, send the UAV as a traffic obsticle to avoid
            for(int i = 0; i < ICAROUS_CONNECTIONS; i++)
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
    }// End of AirVehicleState

    // False indicates that we are ready to process more messages
    return false;
}
}; //namespace service
}; //namespace uxas

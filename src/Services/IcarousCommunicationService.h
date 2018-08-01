// ===============================================================================
// Authors: AFRL/RQQA & NASA/NIA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   IcarousCommunicationService.h
 * Authors: Winston Smith & Paul Coen
 *
 * Created on June 14, 2018, 3:55 PM
 * This file allows connectivity with the CRATOUS system
 * (CRoss Application Translator of Operational Unmanned Systems) 
 * CRATOUS allows cooperative mission planning between UxAS and ICAROUS
 *
 */

#ifndef UXAS_ICAROUSCOMMUNICATIONSERVICE_H
#define UXAS_ICAROUSCOMMUNICATIONSERVICE_H



#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "TypeDefs/UxAS_TypeDefs_Timer.h"

#include "ServiceBase.h"
#include "TypeDefs/UxAS_TypeDefs_String.h"
#include "CallbackTimer.h"

#include "uxas/messages/route/RoutePlan.h"
#include "uxas/messages/route/RoutePlanRequest.h"
#include "uxas/messages/route/RoutePlanResponse.h"

#include "afrl/cmasi/Waypoint.h"
#include "afrl/cmasi/TurnType.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"

#include <sys/types.h>
#include <sys/socket.h>
#include <stdio.h>
#include <string.h>
#include <netinet/in.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory>
#include <errno.h>
#include <cmath>
#include <math.h>
#include <thread>
#include <mutex>
#include <chrono>
#include <semaphore.h>

#define PORT 5557
#define STRING_XML_ICAROUS_CONNECTIONS "NumberOfUAVs"
#define STRING_XML_ICAROUS_ROUTEPLANNER "RoutePlannerUsed"
#define M_PI 3.14159265358979323846

namespace uxas
{
namespace service
{

/*! \class IcarousCommunicationService
 *  \brief This service handles communication with ICAROUS for integration of the two pieces of software.
 *  
 * </ul> @n
 * 
 * Configuration String: <Service Type="IcarousCommunicationService" NumberOfUAVs="n" />
 * 
 * Options:
 *  - NumberOfUAVs - Used to specify the number of UAVs in a scenario
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::MissionCommand
 *  - afrl::cmasi::KeepInZone
 *  - afrl::cmasi::KeepOutZone
 *  - afrl::cmasi::AirVehicleState
 * 
 * Sent Messages:
 *  - uxas::messages::task::TaskResume
 *  - afrl::cmasi::MissionCommand
 *  - afrl::cmasi::VehicleActionCommand
 *  - afrl::cmasi::LoiterAction
 * 
 */

class IcarousCommunicationService : public ServiceBase
{
public:
    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="IcarousCommunicationService". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("IcarousCommunicationService");
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
        return new IcarousCommunicationService;
    };

    IcarousCommunicationService();
    bool isInitializePlan(std::shared_ptr<afrl::cmasi::MissionCommand> & ptr_MissionCommand);

    /** brief Listen to ICAROUS clients for commands*/
    void ICAROUS_listener(int id);

    virtual
    ~IcarousCommunicationService();

private:

    static
    ServiceBase::CreationRegistrar<IcarousCommunicationService> s_registrar;

    /** brief Copy construction not permitted */
    IcarousCommunicationService(IcarousCommunicationService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(IcarousCommunicationService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    bool
    start() override;

    bool
    terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

private:
    // Saved threadIDs of ICAROUS listeners
    std::vector<std::thread> icarousID;
    
    std::vector<float> nominalUAVHorizontalSpeed;
    
    std::vector<float> nominalUAVVerticleSpeed;
    
    std::vector<std::vector<std::shared_ptr<uxas::messages::route::RoutePlanRequest>>> routePlanRequests;
    std::vector<std::shared_ptr<uxas::messages::route::RoutePlanResponse>> routePlanResponses;
    std::vector<uxas::messages::route::RoutePlan*> routePlans;
    std::vector<unsigned int> routePlanCounter;
    std::vector<int> routePlanWaypointCounter;
    std::vector<bool> isRoutePlanResponseInit;
    
    std::vector<bool> deviationFlags;
    
    std::vector<bool> noDeviationReset;
    
    std::vector<float> icarousCommandedSpeed;
    
    // Save the original starting waypoint for each UAV
    std::vector<int64_t> originalStartingWaypoint;
    
    // Create a list of correct headings for the UAV to follow from the MissionCommands
    std::vector<std::vector<float>> headingLists;
    
    // Saved mission commands
    std::vector<std::shared_ptr<afrl::cmasi::MissionCommand>> missionCommands;
    
    // Saved waypoint lists for each instance
    // These are updated as the UAV progresses
    std::vector<std::vector<afrl::cmasi::Waypoint*>> newWaypointLists;
    
    // A boolean to determine when to do waypoint truncation
    std::vector<bool> truncateWaypoint;
    
    // This is to keep an array of translated waypoint indexes to an ordered list
    std::vector<std::vector<int64_t>> icarousClientWaypointLists;
    
    // The current waypoint index a UAV is on
    std::vector<int64_t> currentWaypointIndex;
    
    // The last completed waypoint a UAV has done
    std::vector<int64_t> lastWaypoint;
    
    // A boolean to determine if the first waypoint was initialized
    std::vector<bool> isLastWaypointInitialized;
    
    // A boolean to determine if a mission command was already created and whether or not it should be replaced
    std::vector<bool> resumePointSet;

    // A list of tasks the UAV was doing before being taken over by ICAROUS
    std::vector<std::vector<int64_t>> entityTasks;

    // A boolean to determine when ICAROUS has taken over
    std::vector<bool> icarousTakeoverActive;

    // A boolean to determine when to soft reset ICAROUS
    std::vector<bool> softResetFlag;
    
    // A array of semaphores to control program flow
    sem_t *softResetSemaphores;

    // Dimention 1: ICAROUS instance
    // Dimention 2: Heading | Lat | Long | Alt
    std::vector<std::vector<float>> currentInformation;
    std::vector<std::vector<float>> positionBeforeTakeover;
    
    // One mutex for each ICAROUS instance
    std::mutex *currentInformationMutexes;

    //Number of unique UAVs in the scenario
    int32_t ICAROUS_CONNECTIONS{-1};
    
    // Route planners are defined as:
    // 0 = GRID
    // 1 = ASTAR
    // 2 = RRT
    // 3 = SPLINE
    int32_t ICAROUS_ROUTEPLANNER{-1};

    //This is the number of ICAROUS clients that are permitted
    std::vector<int> client_sockfd;

    //This is an array keeping track of which ICAROUS instances have gotten vehicle waypoint information
    std::vector<bool> has_gotten_waypoints;
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_ICAROUSCOMMUNICATIONSERVICE_H */


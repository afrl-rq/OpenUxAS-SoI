// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   GamsService.h
 * Author: James Edmondson <jedmondson@gmail.com>
 *
 * Created on May 30, 2017, 3:40 PM
 */

#ifndef UXAS_SERVICE_GAMS_SERVICE_H
#define UXAS_SERVICE_GAMS_SERVICE_H


#include "ServiceBase.h"
#include "TypeDefs/UxAS_TypeDefs_String.h"
#include "CallbackTimer.h"

#include "madara/knowledge/KnowledgeBase.h"
#include "madara/threads/Threader.h"
#include "gams/controllers/BaseController.h"
#include "gams/pose/GPSFrame.h"
#include "gams/pose/CartesianFrame.h"


#include "afrl/cmasi/Waypoint.h"
#include "afrl/cmasi/TurnType.h"
#include "afrl/cmasi/MissionCommand.h"

#include <cstdint> // uint32_t
#include <atomic>
#include <vector>
#include <string>

namespace uxas
{
namespace service
{


/*! \class GamsService
 *   \brief A service that provides interfaces to a GAMS-compliant
 *          MADARA knowledge base.
 *
 * 
 * 
 * Configuration String: 
 *  <Service Type="GamsService" />
 * 
 * Options:
 *
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::cmasi::GroundVehicleState
 *  - uxas::madara::MadaraState
 * 
 * Sent Messages:
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::cmasi::GroundVehicleState
 *  - afrl::cmasi::MissionCommand
 *  - uxas::madara::MadaraState
 */



class GamsService : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("GamsService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName()
    {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create()
    {
        return new GamsService;
    };

    GamsService();

    virtual
    ~GamsService();

    
    /**
     * Sends a MadaraState message through the existing UxAS system. This
     * is extremely dirty, but I need a way to interact from the
     * UxASMadaraTransport, and I can't think of a different way to
     * interact with the sendLmcpObjectBroadcastMessage protected function.
     * @param  buffer    encoded MADARA character buffer
     * @param  length    length of the character buffer in bytes
     **/
    void sendBuffer (char * buffer, size_t length);
    
    /**
     * Sends a MissionCommand with a waypoint to UxAS
     * @param  location  location to move to
     **/
    void sendWaypoint (const gams::pose::Position & location);
    
    /**
     * Moves the agent platform to a location.
     * @param   target    the coordinates to move to
     * @param   epsilon   approximation value
     * @return the status of the move operation,
     *         @see gams::platforms::PlatformReturnValues
     **/
    static int move (const gams::pose::Position & location,
      double epsilon = get_accuracy ());
    
    /**
     * Returns the accuracy of the underlying platform
     * @return the accuracy of the platform in meters
     **/
    static double get_accuracy (void);
    
    /**
     * Returns the reference frame of the UxAS platform. Use this when
     * constructing a gams::pose::Position, e.g., for waypoint usage.
     * @return the reference frame used by the GAMS platform (usually GPS)
     **/
    static gams::pose::ReferenceFrame & frame (void);
    
    /**
     * Adds a mapping of an agent prefix to an entity id
     * @param agentPrefix the prefix of GAMS agent
     * @param entityId the entity id of UxAS
     */
    static void mapAgent (const std::string & agentPrefix, int64_t entityId);
    
    /**
     * Retrieves the entityId equivalent for an agent prefix
     * @param agentPrefix the prefix to lookup
     * @return the corresponding entityId
     */
    static int64_t getEntityId (const std::string & agentPrefix);
    
    /**
     * Retrieves the agent prefix equivalent for an entity id
     * @param entityId the entity to lookup
     * @return the corresponding agent prefix
     */
    static std::string getAgentPrefix (int64_t entityId);
    
    /**
     * Sets the logic rate and update send rate.
     * @param hertz      the hertz to execute logic at
     * @param sendHertz  the hertz to send updates at
     **/
    void controllerRun (double hertz, double sendHertz);
    
    /** knowledge base pre-configured with UxAS integration **/
    static ::madara::knowledge::KnowledgeBase s_knowledgeBase;
    
private:

    static
    ServiceBase::CreationRegistrar<GamsService> s_registrar;

    /** brief Copy construction not permitted */
    GamsService(GamsService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(GamsService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    //bool
    //start() override;

    bool
    terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

    /// unique agent id (by default generated from ephemeral bindings)
    std::string m_uniqueId;
    
    /// transport settings 
    madara::transport::QoSTransportSettings m_transportSettings;
    
    /// convenience handle to the thread safe context in the knowledge base
    madara::knowledge::ThreadSafeContext * m_context;
    
    /// data received rules, defined in Transport settings
    madara::knowledge::CompiledExpression  m_onDataReceived;
      
    /// monitor for sending bandwidth usage
    madara::transport::BandwidthMonitor   m_sendMonitor;
      
    /// monitor for receiving bandwidth usage
    madara::transport::BandwidthMonitor   m_receiveMonitor;

    /// scheduler for mimicking target network conditions
    madara::transport::PacketScheduler    m_packetScheduler;
    
    /// controller for GAMS agent
    gams::controllers::BaseController *   m_controller;
    
    /// settings for the GAMS controller
    gams::controllers::ControllerSettings m_controllerSettings;
    
    /// qos-enabled thread manager
    madara::threads::Threader m_threader;
    
    /// map of agents to their corresponding GAMS variable containers
    gams::variables::AgentMap m_agentMap;
    
    /// a list of karl files to evaluate after controller initialization
    std::vector <std::string> m_karlFiles;
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_GAMS_SERVICE_H */


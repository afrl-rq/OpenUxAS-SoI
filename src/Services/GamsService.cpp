// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   GamsService.cpp
 * Author: James Edmondson <jedmondson@gmail.com>
 *
 * Created on May 30, 2017, 3:40 PM
 *
 */


#include "GamsService.h"

#include "UnitConversions.h"
#include "UxAS_TimerManager.h"

#include "madara/logger/GlobalLogger.h"
#include "madara/threads/Threader.h"
#include "madara/knowledge/ContextGuard.h"
#include "madara/knowledge/containers/Map.h"

#include "gams/groups/GroupFixedList.h"
#include "gams/loggers/GlobalLogger.h"

#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/GimbalAngleAction.h"
#include "afrl/cmasi/LoiterAction.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/Waypoint.h"

#include "afrl/impact/GroundVehicleState.h"

#include "uxas/messages/uxnative/IncrementWaypoint.h"

#include "uxas/madara/MadaraState.h"

#include "pugixml.hpp"

#include <iostream>

#define STRING_COMPONENT_NAME "GamsService"

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_COMPONENT_TYPE "GamsService"
#define STRING_XML_VEHICLE_ID "VehicleID"


#define COUT_INFO(MESSAGE) std::cout << "<>GamsService:: " << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>GamsService:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>GamsService:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();

namespace knowledge = madara::knowledge;
namespace transport = madara::transport;
namespace controllers = gams::controllers;
namespace variables = gams::variables;
namespace platforms = gams::platforms;
namespace loggers = gams::loggers;

/// static knowledge base which is configured with UxAS transport
knowledge::KnowledgeBase uxas::service::GamsService::s_knowledgeBase;

// static knowledge base that serves as a local file mutex that does not
// conflict with the s_knowledgeBase
knowledge::KnowledgeBase gamsServiceMutex;

// file local maps stored in the gamsServiceMutex knowledge base
knowledge::containers::Map agentToEntity;
knowledge::containers::Map entityToAgent;

// handle to the gamsServicePlatform
gams::platforms::BasePlatform * gamsServicePlatform (0);

namespace uxas
{
namespace service
{
  /**
   * Transport for UxAS GamsService to convert knowledge to UxAS Messages
   **/
  class UxASMadaraTransport : public transport::Base
  {
  public:
      /**
       * Constructor
       * @param   id                unique identifier (generally host:port)
       * @param   new_settings      settings to apply to the transport
       * @param   context           the knowledge record context
       * @param   service           the calling GamsService
       **/
      UxASMadaraTransport (const std::string & id,
        transport::TransportSettings & new_settings,
        knowledge::KnowledgeBase & knowledge,
        GamsService * service)
      : transport::Base (id, new_settings, knowledge.get_context ()),
        m_service (service)
      {
        // populate variables like buffer_ based on transport settings
        transport::Base::setup ();
      }

      /**
       * Destructor
       **/
      virtual ~UxASMadaraTransport ()
      {

      }
    
      /**
       * Sends a list of updates to the UxAS system
       * @param  modifieds  a list of keys to values of all records that have
       *          been updated and could be sent.
       * @return  result of operation or -1 if we are shutting down
       **/
      virtual long send_data (const knowledge::KnowledgeRecords & modifieds)
      {
        ///Return number of bytes sent or negative for error
        long result (0);
        
        /// Prefix for printing purposes in madara logger
        const char * printPrefix = "UxASMadaraTransport::send_data";

        /// prepare the buffer for sending by filling in all modifieds
        result = prep_send (modifieds, printPrefix);

        /// if the service exists (which it should), send the MadaraState
        if (m_service)
        {
            m_service->sendBuffer(buffer_.get (), (size_t)result);
            
            /// add the bytes sent to the send bandwidth monitor
            send_monitor_.add ((uint32_t)result);
        }

        /// return the buffer size that was sent
        return result;
      }
    
  protected:
      
      /// handle to the GamsService so we can use sendBuffer
      GamsService * m_service;
  };
    

      
  /**
  * GAMS platform for manipulating the UxAS agent
  **/
  class UxASGamsPlatform : public gams::platforms::BasePlatform
  {
  public:
    /**
     * Constructor
     * @param  service    pointer to the GamsService
     * @param  knowledge  context containing variables and values
     * @param  sensors    map of sensor names to sensor information
     * @param  self       self referencing variables for the agent
     **/
    UxASGamsPlatform (
      GamsService * serviceTemp,
      knowledge::KnowledgeBase * knowledge = 0,
      variables::Sensors * sensors = 0,
      variables::Self * self = 0)
            : ::gams::platforms::BasePlatform (knowledge, sensors, self),
                    m_service (serviceTemp)
    {
        // as an example of what to do here, create a coverage sensor
        if (knowledge && sensors)
        {
            // create a coverage sensor
            gams::variables::Sensors::iterator it = sensors->find ("coverage");
            if (it == sensors->end ()) // create coverage sensor
            {
              // get origin
              gams::utility::GPSPosition origin;
              knowledge::containers::NativeDoubleArray origin_container;
              origin_container.set_name (
                "sensor.coverage.origin", *knowledge, 3);
              origin.from_container (origin_container);

              // establish sensor
              gams::variables::Sensor* coverage_sensor =
                new gams::variables::Sensor ("coverage", knowledge, 2.5, origin);
              (*sensors)["coverage"] = coverage_sensor;
            }
            (*sensors_)["coverage"] = (*sensors)["coverage"];
            status_.init_vars (*knowledge, get_id ());

            // create threads
            // end create threads


            /**
            * the following should be set when movement is available in your
            * platform. If on construction, movement should be possible, then
            * feel free to keep this uncommented. Otherwise, set it somewhere else
            * in analyze or somewhere else when appropriate to enable movement.
            * If you never enable movement_available, movement based algorithms are
            * unlikely to ever move with your platform.
            **/
            status_.movement_available = 1;
        }
    }

    /**
     * Destructor
     **/
    virtual ~UxASGamsPlatform ()
    {
        // lock the mutex to ensure we can't destroy platform
        // while moving
        knowledge::ContextGuard guard (gamsServiceMutex);
    }

    /**
     * Polls the sensor environment for useful information. Required.
     * @return number of sensors updated/used
     **/
    virtual int sense (void)
    {
        return platforms::PLATFORM_OK;
    }

    /**
     * Analyzes platform information. Required.
     * @return bitmask status of the platform. @see PlatformAnalyzeStatus.
     **/
    virtual int analyze (void)
    {
        return platforms::PLATFORM_OK;
    }

    /**
     * Gets the name of the platform. Required.
     **/
    virtual std::string get_name () const
    {
        return "UxASGamsPlatform";
    }

    /**
     * Gets the unique identifier of the platform. This should be an
     * alphanumeric identifier that can be used as part of a MADARA
     * variable (e.g. vrep_ant, autonomous_snake, etc.) Required.
     **/
    virtual std::string get_id () const
    {
        return "UxASGamsPlatform";
    }

    /**
     * Gets the position accuracy in meters. Optional.
     * @return position accuracy
     **/
    virtual double get_accuracy (void) const
    {
        // we're assuming 1M accuracy in positioning
        return 70.0;
    }

    /**
     * Gets Location of platform, within its parent frame. Optional.
     * @return Location of platform
     **/
    virtual gams::pose::Position get_location () const
    {
        // we're currently reading location from knowledge base
        // this should be set by the UxAS LMCP processing logic
        gams::pose::Position result (gps_frame);
        result.from_container(self_->agent.location);
        
        return result;
    }

    /**
     * Gets orientation of platform, within its parent frame. Optional.
     * @return Location of platform
     **/
    virtual gams::pose::Orientation get_orientation () const
    {
        // we're currently reading orientation from knowledge base
        // this should be set by the UxAS LMCP processing logic
        gams::pose::Orientation result;
        result.from_container(self_->agent.orientation);
        
        return result;
    }

    /**
     * Gets sensor radius. Optional.
     * @return minimum radius of all available sensors for this platform
     **/
    virtual double get_min_sensor_range () const
    {
        return 5.0;
    }

    /**
     * Gets move speed. Optional.
     * @return speed in meters per second
     **/
    virtual double get_move_speed () const
    {
        // FIXME: definitely not what we want to do here
        // potentially available in VehicleState messages
        return 0.0;
    }

    /**
     * Instructs the agent to return home. Optional.
     * @return the status of the home operation, @see PlatformReturnValues
     **/
    virtual int home (void)
    {
        // once we figure out the 
        gams::pose::Position next (gps_frame);
        next.from_container(self_->agent.home);
        
        return this->move(next, get_accuracy ());
    }

    /**
     * Instructs the agent to land. Optional.
     * @return the status of the land operation, @see PlatformReturnValues
     **/
    virtual int land (void)
    {
        // FIXME: definitely not what we want to do here
        return platforms::PLATFORM_OK;
    }

    /**
     * Moves the platform to a location. Optional.
     * @param   target    the coordinates to move to
     * @param   epsilon   approximation value
     * @return the status of the move operation, @see PlatformReturnValues
     **/
    virtual int move (const gams::pose::Position & location,
      double epsilon)
    {
        gams::pose::Position current (gps_frame);
        current.from_container(self_->agent.location);
        
        if (m_last != location)
        {
            gams::platforms::BasePlatform::move(location, epsilon);
        }
        
        if (location.approximately_equal(current, epsilon))
        {
            madara_logger_ptr_log (loggers::global_logger.get (),
              loggers::LOG_MAJOR,
              "UxASGamsPlatform::move: [%.4f, %.4f, %.4f] ~= [%.4f, %.4f, %.4f]"
              " with %.2f m accuracy. Arrived at location.\n",
              location.lat(), location.lng(), location.alt(), 
              current.lat(), current.lng(), current.alt(), epsilon);

            return platforms::PLATFORM_ARRIVED;
        }
        else
        {
            madara_logger_ptr_log (loggers::global_logger.get (),
              loggers::LOG_MAJOR,
              "UxASGamsPlatform::move: [%.4f, %.4f, %.4f] != [%.4f, %.4f, %.4f]"
              " with %.2f m accuracy. Still moving to location.\n",
              location.lat(), location.lng(), location.alt(), 
              current.lat(), current.lng(), current.alt(), epsilon);

            m_service->sendWaypoint(location);
            return platforms::PLATFORM_MOVING;
        }
    }

    /**
     * Orients the platform to match a given angle. Optional.
     * @param   target    the rotation to move to
     * @param   epsilon   approximation value
     * @return the status of the rotate, @see PlatformReturnValues
     **/
    virtual int orient (const gams::pose::Orientation & target,
      double epsilon)
    {
        // FIXME: definitely not what we want to do here
        return platforms::PLATFORM_OK;
    }

    /**
     * Moves the platform to a pose (location and rotation). Optional.
     *
     * This default implementation calls move and rotate with the
     * Location and Rotation portions of the target Pose. The return value
     * is composed as follows: if either call returns ERROR (0), this call
     * also returns ERROR (0). Otherwise, if BOTH calls return ARRIVED (2),
     * this call also returns ARRIVED (2). Otherwise, this call returns
     * MOVING (1)
     *
     * Overrides might function differently.
     *
     * @param   target        the coordinates to move to
     * @param   loc_epsilon   approximation value for the location
     * @param   rot_epsilon   approximation value for the rotation
     * @return the status of the operation, @see PlatformReturnValues
     **/
    virtual int pose (const gams::pose::Pose & target,
      double loc_epsilon = 0.1, double rot_epsilon = M_PI/16)
    {
        return move (gams::pose::Position(target), loc_epsilon);
    }

    /**
     * Pauses movement, keeps source and dest at current values. Optional.
     **/
    virtual void pause_move (void)
    {
        // FIXME: definitely not what we want to do here 
    }

    /**
     * Set move speed. Optional.
     * @param speed new speed in meters/second
     **/
    virtual void set_move_speed (const double& speed)
    {
        // FIXME: definitely not what we want to do here
    }

    /**
     * Stops movement, resetting source and dest to current location.
     * Optional.
     **/
    virtual void stop_move (void)
    {
        // FIXME: definitely not what we want to do here
    }

    /**
     * Instructs the agent to take off. Optional.
     * @return the status of the takeoff, @see PlatformReturnValues
     **/
    virtual int takeoff (void)
    {
        // FIXME: definitely not what we want to do here
        return platforms::PLATFORM_OK;
    }
    
    /**
     * Returns the reference frame for the platform (e.g. GPS or cartesian)
     **/
    virtual const gams::pose::ReferenceFrame & get_frame (void) const
    {
        return gps_frame;
    }
    
    
    // a default GPS frame
    static gams::pose::GPSFrame  gps_frame;
    
    // a default Cartesian frame
    static gams::pose::CartesianFrame  cartesian_frame;
    
  protected:
      
    /// handle to the GamsService so we can use sendBuffer
    GamsService * m_service;
    
    /// keep track of last unique position
    gams::pose::Position m_last;
    
  }; // end UxASGamsPlatform class
  
/// static reference frames we can use for the UxAS platform (gps preferred)
gams::pose::CartesianFrame  UxASGamsPlatform::cartesian_frame;   
gams::pose::GPSFrame  UxASGamsPlatform::gps_frame;         



  /**
  * A Controller thread for executing GAMS logic and sending updates
  **/
  class ControllerLoop : public ::madara::threads::BaseThread
  {
  public:
    /**
     * Default constructor
     **/
    ControllerLoop (gams::controllers::BaseController * controller)
    : m_controller (controller)
    {
        
    }
    
    /**
     * Destructor
     **/
    virtual ~ControllerLoop ()
    {
    }
    
    /**
      * We do not need an initializer because of the order of operations in
      * the GamsService 
      **/
    virtual void init (::madara::knowledge::KnowledgeBase &)
    {
    }

    /**
      * Executes the main thread logic
      **/
    virtual void run (void)
    {
        // run from the controller configuration settings
        m_controller->run();
    }

  private:
      /// handle to GAMS controller
      gams::controllers::BaseController * m_controller;
  };

void GamsService::mapAgent (const std::string & agentPrefix, int64_t entityId)
{
    if (agentPrefix != "" && entityId > 0)
    {
        std::stringstream entityString;
        entityString << entityId;

        agentToEntity.set (agentPrefix, entityId);
        entityToAgent.set (entityString.str (), agentPrefix);
    }
}
  
int64_t GamsService::getEntityId (const std::string & agentPrefix)
{
    return agentToEntity[agentPrefix].to_integer ();
}
    
std::string GamsService::getAgentPrefix (int64_t entityId)
{
    std::string result;
    
    if (entityId > 0)
    {
        std::stringstream index;
        index << entityId;
    
        knowledge::KnowledgeRecord record = entityToAgent[index.str ()];
        
        if (record.exists())
        {
            result = record.to_string ();
        }
    }
    
    return result;
}

gams::pose::ReferenceFrame & GamsService::frame (void)
{
    return UxASGamsPlatform::gps_frame;
}

double GamsService::get_accuracy (void)
{
    knowledge::ContextGuard guard (gamsServiceMutex);
    
    double accuracy = 70.0;
    
    if (gamsServicePlatform)
    {
        accuracy = gamsServicePlatform->get_accuracy();
    }
    
    return accuracy;
}

int GamsService::move (const gams::pose::Position & location,
      double epsilon)
{
    knowledge::ContextGuard guard (gamsServiceMutex);
    
    // default is set to an error (platform doesn't exist)
    int result = gams::platforms::PLATFORM_ERROR;
    
    if (gamsServicePlatform)
    {
        madara_logger_ptr_log (loggers::global_logger.get (),
          loggers::LOG_MAJOR,
          "GamsService::move: moving to [%.4f, %.4f, %.4f]"
          " with %.2f m accuracy\n",
          location.lat(), location.lng(), location.alt(), epsilon);
    
        result = gamsServicePlatform->move (location, epsilon);
    }
    
    return result;
}
    
GamsService::ServiceBase::CreationRegistrar<GamsService>
GamsService::s_registrar(GamsService::s_registryServiceTypeNames());

GamsService::GamsService()
: ServiceBase(GamsService::s_typeName(), GamsService::s_directoryName()),
  m_context (&(s_knowledgeBase.get_context())),
  m_controller (0), m_threader (s_knowledgeBase) {

};

GamsService::~GamsService() { };

bool
GamsService::configure(const pugi::xml_node& serviceXmlNode)
{
    // set some reasonable defaults (2hz, same send rate, 10s runtime)
    m_controllerSettings.loop_hertz = 2;
    m_controllerSettings.run_time = 10;
    m_controllerSettings.send_hertz = -1;
    
    madara_logger_ptr_log (loggers::global_logger.get (),
        loggers::LOG_MAJOR,
        "GamsService::Starting configure\n");
    
    // set the prefixes for the global maps of agents to entities
    agentToEntity.set_name("agent", gamsServiceMutex);
    entityToAgent.set_name("entity", gamsServiceMutex);
    
    madara_logger_ptr_log (loggers::global_logger.get (),
        loggers::LOG_MINOR,
        "GamsService::Iterating config XML\n");
    
    
    // load settings from the XML file
    for (pugi::xml_node currentXmlNode = serviceXmlNode.first_child();
         currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
    {
        // if we need to load initial knowledge
        if (std::string("Knowledge") == currentXmlNode.name())
        {
            if (!currentXmlNode.attribute("BinaryFile").empty())
            {
                madara_logger_ptr_log (loggers::global_logger.get (),
                    loggers::LOG_MAJOR,
                    "GamsService::Loading knowledge base from %s\n",
                    currentXmlNode.attribute("BinaryFile").as_string());
    
                s_knowledgeBase.load_context(
                    currentXmlNode.attribute("BinaryFile").as_string());
            }
            
            if (!currentXmlNode.attribute("KarlFile").empty())
            {
                madara_logger_ptr_log (loggers::global_logger.get (),
                    loggers::LOG_MAJOR,
                    "GamsService::Evaluating karl file\n");
    
                knowledge::EvalSettings settings;
                settings.treat_globals_as_locals = true;
                
                std::string karlFile = ::madara::utility::file_to_string (
                   currentXmlNode.attribute("KarlFile").as_string());
                
                s_knowledgeBase.evaluate(karlFile, settings);
            }
        }
        // if we need to setup the GamsController
        else if(std::string("GamsController") == currentXmlNode.name())
        {
            madara_logger_ptr_log (loggers::global_logger.get (),
                loggers::LOG_MAJOR,
                "GamsService::config: importing GamsController settings\n");
    
            // retrieve the agent prefix/id
            if (!currentXmlNode.attribute("AgentPrefix").empty())
            {
                m_controllerSettings.agent_prefix =
                        currentXmlNode.attribute("AgentPrefix").as_string();
            }
            
            // retrieve the checkpoint file prefix (includes directories)
            if (!currentXmlNode.attribute("CheckpointPrefix").empty())
            {
                m_controllerSettings.checkpoint_prefix =
                        currentXmlNode.attribute("CheckpointPrefix").as_string();
            }
            
            // checkpoint strategy (0==NONE, 1==ON_LOOP, 2==ON_SEND)
            if (!currentXmlNode.attribute("CheckpointStrategy").empty())
            {
                m_controllerSettings.checkpoint_strategy =
                        currentXmlNode.attribute("CheckpointStrategy").as_int();
            }
            
            // set the GAMS logging level
            if (!currentXmlNode.attribute("GamsLogLevel").empty())
            {
                gams::loggers::global_logger->set_level(
                        currentXmlNode.attribute("GamsLogLevel").as_int());
            }
            
            // set the MADARA logging level
            if (!currentXmlNode.attribute("MadaraLogLevel").empty())
            {
                ::madara::logger::global_logger->set_level(
                        currentXmlNode.attribute("MadaraLogLevel").as_int());
            }
            
            // set the loop hertz
            if (!currentXmlNode.attribute("LoopHertz").empty())
            {
                m_controllerSettings.loop_hertz =
                        currentXmlNode.attribute("LoopHertz").as_double();
            }
            
            // set the send hertz
            if (!currentXmlNode.attribute("SendHertz").empty())
            {
                m_controllerSettings.send_hertz =
                        currentXmlNode.attribute("SendHertz").as_double();
            }
            
            // set the send hertz
            if (!currentXmlNode.attribute("RunTime").empty())
            {
                m_controllerSettings.run_time =
                        currentXmlNode.attribute("RunTime").as_double();
            }
        }
        // if we need to setup the agent mappings
        else if(std::string("Agents") == currentXmlNode.name())
        {
            madara_logger_ptr_log (loggers::global_logger.get (),
                loggers::LOG_MAJOR,
                "GamsService::config: importing agent mappings\n");
    
            // iterate through agent mappings
            for (pugi::xml_node agentNode = currentXmlNode.first_child();
                 agentNode; agentNode = agentNode.next_sibling())
            {
                int64_t entityId = 0;
                std::string agentPrefix = "agent.0";
                
                // retrieve the agent prefix/id
                if (!agentNode.attribute("Prefix").empty())
                {
                    agentPrefix =
                        agentNode.attribute("Prefix").as_string();
                }

                // retrieve the checkpoint file prefix (includes directories)
                if (!agentNode.attribute("EntityId").empty())
                {
                    entityId =
                            agentNode.attribute("EntityId").as_int64();
                }
            
                mapAgent (agentPrefix, entityId);
            }
            
        }
        // if we have logging to setup
        else if(std::string("Logging") == currentXmlNode.name())
        {
            madara_logger_ptr_log (loggers::global_logger.get (),
                loggers::LOG_MAJOR,
                "GamsService::config: importing logging settings\n");
    
            pugi::xml_node madaraNode = currentXmlNode.child("Madara");
            pugi::xml_node gamsNode = currentXmlNode.child("Gams");
            
            if (madaraNode)
            {
                if (!madaraNode.attribute("Level").empty())
                {
                    ::madara::logger::global_logger->set_level (
                        madaraNode.attribute("Level").as_int());
                }
                
                if (!madaraNode.attribute("File").empty())
                {
                    ::madara::logger::global_logger->add_file (
                        madaraNode.attribute("File").as_string());
                }
            }
            if (gamsNode)
            {
                if (!gamsNode.attribute("Level").empty())
                {
                    gams::loggers::global_logger->set_level (
                        gamsNode.attribute("Level").as_int());
                }
                
                if (!gamsNode.attribute("File").empty())
                {
                    gams::loggers::global_logger->add_file (
                        gamsNode.attribute("File").as_string());
                }
            }
        }
        // if we need to setup the agent mappings
        else if(std::string("Groups") == currentXmlNode.name())
        {
            madara_logger_ptr_log (loggers::global_logger.get (),
                loggers::LOG_MAJOR,
                "GamsService::config: importing group settings\n");
    
            // iterate through agent mappings
            for (pugi::xml_node groupNode = currentXmlNode.first_child();
                 groupNode; groupNode = groupNode.next_sibling())
            {
                std::string groupPrefix =
                    groupNode.attribute("Prefix").as_string();
                
                if (groupPrefix != "")
                {
                    gams::groups::GroupFixedList group (
                        groupPrefix, &s_knowledgeBase);
                    gams::groups::AgentVector members;
                
                    // iterate through agent mappings
                    for (pugi::xml_node memberNode = groupNode.first_child();
                         memberNode; memberNode = memberNode.next_sibling())
                    {
                        if (!memberNode.attribute("Name").empty())
                        {
                            members.push_back (
                                memberNode.attribute("Name").as_string());
                        }
                    }
                    group.add_members(members);
                }
            }
            
        }
    }

    // save the agent mapping for forensics
    gamsServiceMutex.save_context(
        m_controllerSettings.checkpoint_prefix + "_config_gamsServiceMutex.kb");
    // save the agent mapping for forensics
    s_knowledgeBase.save_context(
        m_controllerSettings.checkpoint_prefix + "_config_knowledgeBase.kb");
    
    // attach the MadaraTransport for knowledge modifications to UxAS messages
    s_knowledgeBase.attach_transport (
      new UxASMadaraTransport (m_uniqueId, m_transportSettings, s_knowledgeBase,
            this));
    
    m_controller = new gams::controllers::BaseController (s_knowledgeBase,
        m_controllerSettings);
    
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    addSubscriptionAddress(afrl::impact::GroundVehicleState::Subscription);
    addSubscriptionAddress(uxas::madara::MadaraState::Subscription);
    
    return true;
}

bool
GamsService::initialize()
{
    bool bSuccess(true);

    madara_logger_ptr_log (loggers::global_logger.get (),
        loggers::LOG_MAJOR, "GamsService::initialize\n");
    
    // create the UxAS platform
    m_controller->init_platform(new UxASGamsPlatform(this));
    m_controller->init_algorithm("null");
    
    {
        ::madara::knowledge::ContextGuard lock (gamsServiceMutex);
        gamsServicePlatform = m_controller->get_platform ();
    }
    
    // save the agent mapping for forensics
    gamsServiceMutex.save_context(
        m_controllerSettings.checkpoint_prefix + "_init_gamsServiceMutex.kb");
    // save the agent mapping for forensics
    s_knowledgeBase.save_context(
        m_controllerSettings.checkpoint_prefix + "_init_knowledgeBase.kb");
    
    // run at 2hz, sending at 1hz, forever (-1)
    m_threader.run (1.0/m_controllerSettings.run_time, "controller",
      new service::ControllerLoop (m_controller));
    
    
    return (bSuccess);
};

bool
GamsService::terminate()
{
    // lock the knowledge base and set platform to null
    {
        ::madara::knowledge::ContextGuard lock (gamsServiceMutex);
        gamsServicePlatform = 0;
    }
    
    m_threader.terminate();
    m_threader.wait ();
    
    // save the agent mapping for forensics
    gamsServiceMutex.save_context(
        m_controllerSettings.checkpoint_prefix + "_term_gamsServiceMutex.kb");
    // save the agent mapping for forensics
    s_knowledgeBase.save_context(
        m_controllerSettings.checkpoint_prefix + "_term_knowledgeBase.kb");
    
    // cleanup the GAMS controller
    delete m_controller;
    
    return true;
}


void
GamsService::sendBuffer (char * buffer, size_t length)
{
    auto newMessage = std::shared_ptr<uxas::madara::MadaraState>(new uxas::madara::MadaraState);
    
    std::vector <uint8_t> contents;
    contents.resize (length);
    for (size_t i = 0; i < length; ++i)
    {
        contents[i] = (uint8_t)buffer[i];
    }
    
    // direct access to vectors in LMCP, so directly assign to message contents
    newMessage->getContents().assign(contents.begin(), contents.end());
    
    // only send shared pointers to LMCP objects
    sendSharedLmcpObjectBroadcastMessage(newMessage);
}

void
GamsService::sendWaypoint (const gams::pose::Position & location)
{
    // create the next waypoint
    afrl::cmasi::Waypoint * nextPoint = new afrl::cmasi::Waypoint ();
    nextPoint->setLatitude(location.lat());
    nextPoint->setLongitude(location.lng());
    nextPoint->setAltitude(location.alt());
    nextPoint->setNumber(1);
    nextPoint->setNextWaypoint(1);
    nextPoint->setSpeed(22.0);  // TODO: get from AirVehicleConfiguration
    
    // create a mission with the waypoint as its only member
    auto newMission = std::shared_ptr<afrl::cmasi::MissionCommand>(new afrl::cmasi::MissionCommand);
    newMission->getWaypointList().push_back (nextPoint);
        
    // indicate that the first waypoint is the waypoint to use
    newMission->setFirstWaypoint(1);
    
    newMission->setVehicleID(this->m_entityId);
        
    // only send shared pointers to LMCP objects
    sendSharedLmcpObjectBroadcastMessage(newMission);
}

void
GamsService::controllerRun (double hertz,
    double sendHertz)
{
    m_controllerSettings.loop_hertz = hertz;
    m_controllerSettings.send_hertz = sendHertz;
    
    if (m_controller != 0)
    {
        m_controller->get_platform ()->get_self()->agent.loop_hz = hertz;
        m_controller->get_platform ()->get_self()->agent.send_hz = sendHertz;
    }
}

bool
GamsService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object.get()) ||
        afrl::impact::isGroundVehicleState(receivedLmcpMessage->m_object.get()) ||
        afrl::cmasi::isEntityState(receivedLmcpMessage->m_object.get()))
    {
        // retrieve a EntityState pointer for querying
        std::shared_ptr<afrl::cmasi::EntityState> message =
            std::static_pointer_cast<afrl::cmasi::EntityState>(
                receivedLmcpMessage->m_object);
        
        int64_t entityId = message->getID();
        std::string agentPrefix = getAgentPrefix (entityId);

        madara_logger_ptr_log (loggers::global_logger.get (),
            loggers::LOG_MAJOR,
            "GamsService: Processing entity(%d), agent(%s)\n",
            (int)entityId, agentPrefix.c_str ());
        
        variables::Agent agent;
        if (agentPrefix != "")
        {
            variables::AgentMap::iterator found = m_agentMap.find (agentPrefix);

            if (found != m_agentMap.end ())
            {
                agent = found->second;
            }
            else
            {
                m_agentMap[agentPrefix].init_vars (
                    s_knowledgeBase, agentPrefix);
                agent = m_agentMap[agentPrefix];
            }
        }
        else
        {
            std::stringstream newprefix;
            newprefix << "agent.";
            newprefix << entityId;
            
            // build a new entityId <-> agentPrefix mapping
            GamsService::mapAgent(newprefix.str(), entityId);
            
            // create an entry in the knowledge base
            m_agentMap[newprefix.str()].init_vars (
                s_knowledgeBase, newprefix.str());
            agent = m_agentMap[newprefix.str()];
        }
        
        gams::pose::Position currentPosition (UxASGamsPlatform::gps_frame);        
        afrl::cmasi::Location3D * location = message->getLocation();
        
        currentPosition.lat(location->getLatitude());
        currentPosition.lng(location->getLongitude());
        currentPosition.alt(location->getAltitude());
        
        currentPosition.to_container(agent.location);
        
        agent.battery_remaining = message->getEnergyAvailable();
    }
    else if (uxas::madara::isMadaraState (receivedLmcpMessage->m_object.get()))
    {
        // clone the LMCP message into a MadaraState structure
        std::shared_ptr<uxas::madara::MadaraState> ptr_MadaraState(
            static_cast<uxas::madara::MadaraState *> (
                receivedLmcpMessage->m_object.get()));
        
        
        // contents are returned as a byte vector. Convert that into a char[]
        std::vector<uint8_t> bufferVector = ptr_MadaraState->getContents ();
        
        char * buffer = new char [bufferVector.size ()];
        if (buffer)
        {
            for (size_t i = 0; i < bufferVector.size (); ++i)
            {
                buffer[i] = (char) bufferVector[i];
            }
        }
        
        // keep track of records for rebroadcast, but don't do so (yet)
        knowledge::KnowledgeMap rebroadcastRecords;
        
        // if we want to look at the MADARA message header after
        transport::MessageHeader * header = 0;
        
        // a print prefix for logging
        const char * printPrefix = "GamsService::processReceivedLmcpMessage";
        
        transport::process_received_update (buffer,
            (ssize_t)bufferVector.size (),
            m_uniqueId,
            *m_context,
            m_transportSettings,
            m_sendMonitor, m_receiveMonitor, rebroadcastRecords,
            m_onDataReceived,
            printPrefix,
            receivedLmcpMessage->m_attributes->getSourceEntityId ().c_str (),
            header);
    }

    // save the agent mapping for forensics
    gamsServiceMutex.save_context(
        m_controllerSettings.checkpoint_prefix + "_last_gamsServiceMutex.kb");
    // save the agent mapping for forensics
    s_knowledgeBase.save_context(
        m_controllerSettings.checkpoint_prefix + "_last_knowledgeBase.kb");
    
    return false;
};


} //namespace service
} //namespace uxas

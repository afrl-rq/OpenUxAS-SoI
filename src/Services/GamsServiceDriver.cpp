// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   GamsServiceDriver.cpp
 * Author: James Edmondson <jedmondson@gmail.com>
 *
 * Created on May 30, 2017, 3:40 PM
 *
 */


#include "GamsServiceDriver.h"
#include "GamsService.h"

#include "UnitConversions.h"
#include "UxAS_TimerManager.h"

#include "madara/logger/GlobalLogger.h"
#include "madara/threads/Threader.h"
#include "madara/knowledge/ContextGuard.h"
#include "madara/knowledge/containers/Map.h"
#include "madara/utility/Utility.h"

#include "gams/groups/GroupFixedList.h"
#include "gams/loggers/GlobalLogger.h"
#include "gams/utility/Position.h"

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

#define STRING_COMPONENT_NAME "GamsServiceDriver"

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_COMPONENT_TYPE "GamsServiceDriver"
#define STRING_XML_VEHICLE_ID "VehicleID"


#define COUT_INFO(MESSAGE) std::cout << "<>GamsServiceDriver:: " << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>GamsServiceDriver:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>GamsServiceDriver:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();

namespace knowledge = madara::knowledge;
namespace transport = madara::transport;
namespace controllers = gams::controllers;
namespace variables = gams::variables;
namespace platforms = gams::platforms;

namespace uxas
{
namespace service
{


  /**
  * A periodic thread for executing GamsService drivers
  **/
  class GamsDriverThread : public ::madara::threads::BaseThread
  {
  public:
    /**
     * Default constructor
     **/
    GamsDriverThread (const gams::pose::Positions & waypoints)
    : m_waypoints (waypoints), m_current (0)
    {
        
    }
    
    /**
     * Destructor
     **/
    virtual ~GamsDriverThread ()
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
        gams::loggers::global_logger->log(gams::loggers::LOG_ALWAYS,
            "GamsDriverThread::run: waypoint index is %d of %d\n",
            (int)m_current, (int)m_waypoints.size ());
    
        /// try to move to current waypoint
        if (m_current < m_waypoints.size () &&
            GamsService::move (m_waypoints[m_current])
            == gams::platforms::PLATFORM_ARRIVED)
        {
            gams::loggers::global_logger->log(gams::loggers::LOG_ALWAYS,
                "GamsDriverThread::run: moving to waypoint %d of %d\n",
                (int)m_current, (int)m_waypoints.size ());
    
            ++m_current;
        }
        else if (m_current >= m_waypoints.size ())
        {
            gams::loggers::global_logger->log(gams::loggers::LOG_ALWAYS,
                "GamsDriverThread::run: end of waypoint list\n");
        }
        else
        {
            gams::loggers::global_logger->log(gams::loggers::LOG_ALWAYS,
                "GamsDriverThread::run: still moving to waypoint\n");
        }
    }

  private:
      /// list of waypoints to go to
      gams::pose::Positions m_waypoints;
      
      /// curWaypoint
      size_t m_current;
  };

    
GamsServiceDriver::ServiceBase::CreationRegistrar<GamsServiceDriver>
GamsServiceDriver::s_registrar(GamsServiceDriver::s_registryServiceTypeNames());

GamsServiceDriver::GamsServiceDriver()
: ServiceBase(GamsServiceDriver::s_typeName(), GamsServiceDriver::s_directoryName()),
  m_checkpointPrefix ("checkpoints/checkpoint"), m_threader (m_knowledgeBase) {

    UXAS_LOG_ERROR("GamsServiceDriver::constr:: sanity check");
};

GamsServiceDriver::~GamsServiceDriver() { };

bool
GamsServiceDriver::configure(const pugi::xml_node& serviceXmlNode)
{
    gams::loggers::global_logger->log(gams::loggers::LOG_ALWAYS,
        "GamsServiceDriver::Starting configure\n");
    
    // load settings from the XML file
    for (pugi::xml_node currentXmlNode = serviceXmlNode.first_child();
         currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
    {
        // if we need to load initial knowledge
        if (std::string("Knowledge") == currentXmlNode.name())
        {
            knowledge::KnowledgeBase * context = &GamsService::s_knowledgeBase;
            
            // if they define Type at all, then use the private knowledge base
            if (!currentXmlNode.attribute("Type").empty())
            {
                context = &m_knowledgeBase;
            }
            
            if (!currentXmlNode.attribute("BinaryFile").empty())
            {
                gams::loggers::global_logger->log(gams::loggers::LOG_ALWAYS,
                    "GamsServiceDriver::Loading knowledge base from %s\n",
                    currentXmlNode.attribute("BinaryFile").as_string());
    
                context->load_context(
                    currentXmlNode.attribute("BinaryFile").as_string());
            }
            
            if (!currentXmlNode.attribute("KarlFile").empty())
            {
                gams::loggers::global_logger->log(gams::loggers::LOG_ALWAYS,
                    "GamsServiceDriver::Evaluating karl file %s\n",
                    currentXmlNode.attribute("KarlFile").as_string());
    
                knowledge::EvalSettings settings;
                settings.treat_globals_as_locals = true;
                
                std::string karlFile = ::madara::utility::file_to_string (
                   currentXmlNode.attribute("KarlFile").as_string());
                
                context->evaluate(karlFile, settings);
            }
        }
        // if we need to load initial knowledge
        if (std::string("Waypoint") == currentXmlNode.name())
        {
            gams::pose::Position nextPosition (GamsService::frame ());
            
            if (!currentXmlNode.attribute("Latitude").empty())
            {
                nextPosition.lat(
                    currentXmlNode.attribute("Latitude").as_double());
            }
            if (!currentXmlNode.attribute("Longitude").empty())
            {
                nextPosition.lng(
                    currentXmlNode.attribute("Longitude").as_double());
            }
            if (!currentXmlNode.attribute("Altitude").empty())
            {
                nextPosition.alt(
                    currentXmlNode.attribute("Altitude").as_double());
            }

            gams::loggers::global_logger->log(gams::loggers::LOG_ALWAYS,
                "GamsServiceDriver::config: adding waypoint [%.4f,%.4f,%.4f]\n",
                nextPosition.lat(), nextPosition.lng(), nextPosition.alt());

            this->m_waypoints.push_back (nextPosition);
        }
    }

    // save the agent mapping for forensics
    m_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_config_privatekb.kb");
    // save the agent mapping for forensics
    GamsService::s_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_config_staticknowledgeBase.kb");
    
    gams::loggers::global_logger->log(gams::loggers::LOG_ALWAYS,
        "GamsServiceDriver::config: ended up with %d waypoints\n",
        this->m_waypoints.size());

    return true;
}

bool
GamsServiceDriver::initialize()
{
    bool bSuccess(true);

    gams::loggers::global_logger->log(0, "GamsServiceDriver::initialize\n");
    
    // save the agent mapping for forensics
    m_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_init_privatekb.kb");
    // save the agent mapping for forensics
    GamsService::s_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_init_staticknowledgeBase.kb");
    
    
    // run at 1hz, forever (-1)
    m_threader.run (1.0, "controller",
      new GamsDriverThread (this->m_waypoints));
    
    
    return (bSuccess);
};

bool
GamsServiceDriver::terminate()
{
    // save the agent mapping for forensics
    m_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_term_privatekb.kb");
    // save the agent mapping for forensics
    GamsService::s_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_term_staticknowledgeBase.kb");
    
    return true;
}


bool
GamsServiceDriver::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    return false;
};


} //namespace service
} //namespace uxas

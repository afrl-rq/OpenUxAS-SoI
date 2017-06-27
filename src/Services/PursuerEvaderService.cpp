// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   PursuerEvaderService.cpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on June 22, 2017, 10:00 AM
 *
 */


#include "PursuerEvaderService.hpp"
#include "GamsService.h"

#include "UnitConversions.h"
#include "UxAS_TimerManager.h"

#include "madara/logger/GlobalLogger.h"
#include "madara/threads/Threader.h"
#include "madara/knowledge/ContextGuard.h"
#include "madara/knowledge/containers/Map.h"
#include "madara/utility/Utility.h"
#include "madara/knowledge/containers/Integer.h"

#include "gams/groups/GroupFixedList.h"
#include "gams/loggers/GlobalLogger.h"
#include "gams/utility/Position.h"
#include "gams/variables/Agent.h"

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

#define STRING_COMPONENT_NAME "PursuerEvaderService"

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_COMPONENT_TYPE "PursuerEvaderService"
#define STRING_XML_VEHICLE_ID "VehicleID"


#define COUT_INFO(MESSAGE) std::cout << "<>PursuerEvaderService:: " << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>PursuerEvaderService:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>PursuerEvaderService:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();

namespace knowledge = madara::knowledge;
namespace transport = madara::transport;
namespace controllers = gams::controllers;
namespace variables = gams::variables;
namespace platforms = gams::platforms;
namespace logger = madara::logger;

namespace
{
    //-- minimum and maximum latitide and longitude of the visible
    //-- map area
    const double LAT_MIN = 45.296;
    const double LAT_MAX = 45.35;
    const double LNG_MIN = -121.02;
    const double LNG_MAX = -120.91;
    const double CELL_LAT = (LAT_MAX - LAT_MIN) / 9;
    const double CELL_LNG = (LNG_MAX - LNG_MIN) / 9;

    //-- compute the location that the evader should go to given the
    //-- current evader and pursuer locations
    gams::pose::Position EvaderTarget(const gams::pose::Position &pursuerPos,
                                      const gams::pose::Position &evaderPos)
    {
        gams::pose::Position res(uxas::service::GamsService::frame());
        res.alt(evaderPos.alt());

        if(evaderPos.lat() <= pursuerPos.lat())
        {
            if(evaderPos.lng() <= pursuerPos.lng())
            {
                res.lat(LAT_MIN);
                res.lng(LNG_MIN);
            }
            else
            {
                res.lat(LAT_MIN);
                res.lng(LNG_MAX);
            }
        }
        else
        {
            if(evaderPos.lng() <= pursuerPos.lng())
            {
                res.lat(LAT_MAX);
                res.lng(LNG_MIN);
            }
            else
            {
                res.lat(LAT_MAX);
                res.lng(LNG_MAX);
            }
        }
        
        return res;
    }
}

namespace uxas
{
namespace service
{


  /**
  * A periodic thread for executing GamsService drivers
  **/
  class PursuerEvaderThread : public ::madara::threads::BaseThread
  {
  public:
    /**
     * Default constructor
     **/
    PursuerEvaderThread (const gams::pose::Positions & waypoints,
                         logger::Logger & logger,
                         bool isPursuer,
                         gams::variables::Agent & pursuer,
                         gams::variables::Agent & evader)
    : m_waypoints (waypoints), m_current (0), m_logger (logger),
      m_isPursuer(isPursuer), m_pursuer (pursuer), m_evader (evader)
    {
    }
    
    /**
     * Destructor
     **/
    virtual ~PursuerEvaderThread ()
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
        // EXAMPLE: using specific logging levels
        madara_logger_log (m_logger, logger::LOG_MAJOR,
            "PursuerEvaderThread::run: pursuer.location is [%s], evader.location is [%s]\n",
            m_pursuer.location.to_record ().to_string ().c_str (),
            m_evader.location.to_record ().to_string ().c_str ());

        gams::pose::Position pursuerPos(GamsService::frame());
        pursuerPos.from_container(m_pursuer.location);

        gams::pose::Position evaderPos(GamsService::frame());
        evaderPos.from_container(m_evader.location);

        if(m_isPursuer)
            GamsService::move(evaderPos, NULL);
        else
            GamsService::move(EvaderTarget(pursuerPos, evaderPos), NULL);
    }

  private:
      /// list of waypoints to go to
      gams::pose::Positions m_waypoints;
      
      /// curWaypoint
      size_t m_current;
      
      logger::Logger & m_logger;

      bool m_isPursuer;
      gams::variables::Agent & m_pursuer;
      gams::variables::Agent & m_evader;
  };

    
PursuerEvaderService::ServiceBase::CreationRegistrar<PursuerEvaderService>
PursuerEvaderService::s_registrar(PursuerEvaderService::s_registryServiceTypeNames());

PursuerEvaderService::PursuerEvaderService()
: ServiceBase(PursuerEvaderService::s_typeName(), PursuerEvaderService::s_directoryName()),
  m_checkpointPrefix ("checkpoints/checkpoint"), m_threader (m_knowledgeBase) {

    // EXAMPLE: by default, MADARA loggers log to stderr. We will later
    // stop logging to stderr and only log to a file
    madara_logger_log (m_logger, logger::LOG_ALWAYS,
        "PursuerEvaderService::constr:: sanity check");
};

PursuerEvaderService::~PursuerEvaderService() { };

bool
PursuerEvaderService::configure(const pugi::xml_node& serviceXmlNode)
{
    // EXAMPLE of using a custom MADARA logger that just goes to a file
    // this makes a private log for your service at an arbitrary level
    m_logger.set_level(4);
    m_logger.add_file("PursuerEvaderServiceLog.txt");

    // the variables are initialized so you can do pursuer.location
    m_pursuer.init_vars (GamsService::s_knowledgeBase, "agent.0");
    m_evader.init_vars (GamsService::s_knowledgeBase, "agent.1");
    
    madara_logger_log (m_logger, logger::LOG_ALWAYS,
        "PursuerEvaderService::Starting configure\n");
    
    // load settings from the XML file
    for (pugi::xml_node currentXmlNode = serviceXmlNode.first_child();
         currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
    {
        // if we need to load initial knowledge
        if (std::string("Role") == currentXmlNode.name())
        {            
            if (!currentXmlNode.attribute("Name").empty())
            {
                std::cerr << "Role name = " << currentXmlNode.attribute("Name").as_string() << '\n';
                if(std::string("Pursuer") == currentXmlNode.attribute("Name").as_string())
                {
                    isPursuer = true;
                    std::cerr << "Node is a pursuer ...\n";
                }
                else
                {
                    std::cerr << "Node is an evader ...\n";
                    
                }
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

            madara_logger_log (m_logger, logger::LOG_ALWAYS,
                "PursuerEvaderService::config: adding waypoint [%.4f,%.4f,%.4f]\n",
                nextPosition.lat(), nextPosition.lng(), nextPosition.alt());

            m_waypoints.push_back (nextPosition);
        }
    }

    // save the agent mapping for forensics
    m_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_config_privatekb.kb");
    // save the agent mapping for forensics
    GamsService::s_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_config_staticknowledgeBase.kb");
    
    madara_logger_log (m_logger, logger::LOG_ALWAYS,
        "PursuerEvaderService::config: ended up with %d waypoints\n",
        this->m_waypoints.size());

    return true;
}

bool
PursuerEvaderService::initialize()
{
    bool bSuccess(true);

    
    madara_logger_log (m_logger, logger::LOG_ALWAYS,
        "PursuerEvaderService::initialize\n");
    
    // save the agent mapping for forensics
    m_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_init_privatekb.kb");
    // save the agent mapping for forensics
    GamsService::s_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_init_staticknowledgeBase.kb");
    
    // EXAMPLE of creating a container that points into the global KB
    ::madara::knowledge::containers::Integer priority;
    priority.set_name ("agent.0.priority", GamsService::s_knowledgeBase);
    
    // run at 1hz, forever (-1)
    m_threader.run (1.0, "controller",
                    new PursuerEvaderThread (this->m_waypoints, this->m_logger,
                                             this->isPursuer, this->m_pursuer, this->m_evader));
    
    
    return (bSuccess);
};

bool
PursuerEvaderService::terminate()
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
PursuerEvaderService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    return false;
};


} //namespace service
} //namespace uxas

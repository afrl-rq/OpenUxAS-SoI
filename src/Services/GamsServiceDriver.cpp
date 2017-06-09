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
    GamsDriverThread ()
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
        
    }

  private:
      /// handle to GAMS controller
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
    }

    // save the agent mapping for forensics
    m_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_config_privatekb.kb");
    // save the agent mapping for forensics
    GamsService::s_knowledgeBase.save_context(
        m_checkpointPrefix + "_gsd_config_staticknowledgeBase.kb");
    
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
      new service::GamsDriverThread ());
    
    
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

// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   GamsServiceDriver.h
 * Author: James Edmondson <jedmondson@gmail.com>
 *
 * Created on May 30, 2017, 3:40 PM
 */

#ifndef UXAS_SERVICE_COLLISION_AVOIDANCE_SERVICE_HPP
#define UXAS_SERVICE_COLLISION_AVOIDANCE_SERVICE_HPP


#include "ServiceBase.h"
#include "GamsService.h"
#include "TypeDefs/UxAS_TypeDefs_String.h"
#include "CallbackTimer.h"

#include "madara/knowledge/KnowledgeBase.h"
#include "madara/threads/Threader.h"
#include "gams/pose/Position.h"


#include "afrl/cmasi/Waypoint.h"
#include "afrl/cmasi/TurnType.h"
#include "afrl/cmasi/MissionCommand.h"

#include <cstdint> // uint32_t
#include <atomic>

namespace uxas
{
namespace service
{


/*! \class CollisionAvoidanceService
 *   \brief A service that implements a collision avoidance protocol.
 *
 * 
 * 
 * Configuration String: 
 *  <Service Type="CollisionAvoidanceService" />
 * 
 * Options:
 *
 * 
 * Subscribed Messages:
 * 
 * Sent Messages:
 */



class CollisionAvoidanceService : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("CollisionAvoidanceService");
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
        return new CollisionAvoidanceService;
    };

    CollisionAvoidanceService();

    virtual
    ~CollisionAvoidanceService();

    
private:

    static
    ServiceBase::CreationRegistrar<CollisionAvoidanceService> s_registrar;

    /** brief Copy construction not permitted */
    CollisionAvoidanceService(CollisionAvoidanceService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(CollisionAvoidanceService const&) = delete;

    void
    read_arguments(const pugi::xml_node& serviceXmlNode);

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

protected:
    
    std::string m_checkpointPrefix;
    
    // private knowledge base
    madara::knowledge::KnowledgeBase m_knowledgeBase;
    
    /// qos-enabled thread manager
    madara::threads::Threader m_threader;

    /// list of waypoints to move to
    gams::pose::Positions m_waypoints;
    
    /// private logger for our service
    madara::logger::Logger m_logger;
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_GAMSDRIVER_SERVICE_H */


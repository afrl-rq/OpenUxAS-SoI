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


#include "afrl/cmasi/Waypoint.h"
#include "afrl/cmasi/TurnType.h"
#include "afrl/cmasi/MissionCommand.h"

#include <cstdint> // uint32_t

namespace uxas
{
namespace service
{


/*! \class GamsService
 *   \brief A service that provides interfaces to GAMS and MADARA middlewares.
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
 * 
 * Sent Messages:
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::cmasi::GroundVehicleState
 *  - afrl::cmasi::MissionCommand
 * 
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

};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_GAMS_SERVICE_H */


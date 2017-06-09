// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_WaypointPlanManager.h
 * Author: steve
 *
 * Created on December 16, 2014, 4:47 PM
 */

#ifndef UXAS_SERVICE_WAYPOINT_2_SEL4_SERVICE_H
#define UXAS_SERVICE_WAYPOINT_2_SEL4_SERVICE_H

#include "ServiceBase.h"
#include "TypeDefs/UxAS_TypeDefs_String.h"
#include "CallbackTimer.h"


#include "afrl/cmasi/Waypoint.h"
#include "afrl/cmasi/MissionCommand.h"

#include <cstdint> // uint32_t

namespace uxas
{
namespace service
{



class Waypoint2Sel4Service : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("Waypoint2Sel4Service");
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
        return new Waypoint2Sel4Service;
    };

    Waypoint2Sel4Service();

    virtual
    ~Waypoint2Sel4Service();


private:

    static
    ServiceBase::CreationRegistrar<Waypoint2Sel4Service> s_registrar;

    /** brief Copy construction not permitted */
    Waypoint2Sel4Service(Waypoint2Sel4Service const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(Waypoint2Sel4Service const&) = delete;

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

protected:


    int64_t m_vehicleID = {-1}; // need a vehicle ID or can't do anything


};

}; //namespace service
}; //namespace uxas

#endif


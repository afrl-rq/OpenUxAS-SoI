// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   LoiterLeash.h
 * Author: derek
 *
 * Created on Jan 20, 2018, 12:21 PM
 */

#ifndef UXAS_LOITERLEASH_H
#define UXAS_LOITERLEASH_H

#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "TypeDefs/UxAS_TypeDefs_Timer.h"

namespace uxas
{
namespace service
{

/*! \class LoiterLeash
 *  \brief Converts heading and heading-rate commands into a continuously updated
 *  loiter waypoint projected out in front of the vehicle.
 *
 *  In order to ensure that direct heading commands respect airspace constraints,
 *  the LoiterLeash service will lead the aircraft with a "leash", a waypoint
 *  projected out a fixed distance that when followed approximates the desired
 *  heading but is guaranteed to remain in clear airspace.
 * 
 *  The LoiterLeash service will estimate the time step between air vehicle
 *  states to allow conversion of heading-rate commands to direct heading commands.
 *  The desired heading is then used to project a loiter out from the current
 *  vehicle position in the desired direction, terminating in a loiter. If the
 *  loiter would intersect or fall outside of allowable airspace, then the
 *  closest point that would all the loiter to feasibly fit is used.
 * 
 * Configuration String: <Service Type="LoiterLeash" />
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::EntityState
 *  - afrl::cmasi::EntityConfiguration
 *  - uxas::messages::route::RoutePlanResponse
 *  - uxas::messages::uxnative::SafeHeadingAction
 * 
 * Sent Messages:
 *  - afrl::messages::route::RoutePlanRequest
 *  - afrl::cmasi::MissionCommand
 * 
 */

class LoiterLeash : public ServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="LoiterLeash". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("LoiterLeash");
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
        return new LoiterLeash;
    };

    LoiterLeash();

    virtual
    ~LoiterLeash();

private:

    static
    ServiceBase::CreationRegistrar<LoiterLeash> s_registrar;

    /** brief Copy construction not permitted */
    LoiterLeash(LoiterLeash const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(LoiterLeash const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


private:
    /*! \brief  Time-step estimator window*/
    std::deque<double> m_TimeStepWindow;
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_LOITERLEASH_H */


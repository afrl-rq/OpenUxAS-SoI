// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_OpRegionState.h
 * Author: derek
 *
 * Created on Aug 2, 2015, 8:21 AM
 */

#ifndef UXAS_SERVICE_OPERATING_REGION_STATE_SERVICE_H
#define UXAS_SERVICE_OPERATING_REGION_STATE_SERVICE_H



#include "ServiceBase.h"
#include "afrl/cmasi/CMASI.h"
#include "afrl/impact/WaterZone.h"
#include <cstdint>

namespace uxas
{
namespace service
{

/*! \class OperatingRegionStateService
 *
 * \brief  
 * 
 * Configuration String: 
 *  <Service Type="OperatingRegionStateService" AdditionalPadding="0.0" />
 * 
 * Options:
 *  - AdditionalPadding: adds this value to the normal padding of all zones
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::KeepInZone
 *  - afrl::cmasi::KeepOutZone
 *  - afrl::cmasi::RemoveZones
 * 
 * Sent Messages:
 *  - afrl::cmasi::OperatingRegion
 * 
 */

class OperatingRegionStateService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("OperatingRegionStateService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create() {
        return new OperatingRegionStateService;
    };

    OperatingRegionStateService();

    virtual
    ~OperatingRegionStateService();

private:

    static
    ServiceBase::CreationRegistrar<OperatingRegionStateService> s_registrar;

    /** brief Copy construction not permitted */
    OperatingRegionStateService(OperatingRegionStateService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(OperatingRegionStateService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

    // storage
    std::shared_ptr<afrl::cmasi::OperatingRegion> m_region;
    double m_additionalPadding{0.0};

};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_OPERATING_REGION_STATE_SERVICE_H */

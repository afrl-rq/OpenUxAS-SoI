// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   DAIDALUS_WCV_Detection.h
 * Author: SeanR
 *
 * Created on February 5, 2018, 5:55 PM
 */

#ifndef UXAS_00_SERVICE_TEMPLATE_H
#define UXAS_00_SERVICE_TEMPLATE_H



#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "TypeDefs/UxAS_TypeDefs_Timer.h"

namespace uxas
{
namespace service
{

/*! \DAIDALUS_WCV_Detection Serive
 * This service is used to interface the NASA's DAIDALUS code for Well Clear Violation Detections
 */

class DAIDALUS_WCV_Detection : public ServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="DAIDALUS_WCV_Detection". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("DAIDALUS_WCV_Detection");
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
        return new DAIDALUS_WCV_Detection;
    };

    DAIDALUS_WCV_Detection();

    virtual
    ~DAIDALUS_WCV_Detection();

private:

    static
    ServiceBase::CreationRegistrar<DAIDALUS_WCV_Detection> s_registrar;

    /** brief Copy construction not permitted */
    DAIDALUS_WCV_Detection(DAIDALUS_WCV_Detection const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(DAIDALUS_WCV_Detection const&) = delete;

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


private:
    // storage for the option entries
    std::string m_option01 = std::string("No Option 1");
    int32_t m_option02{0};
};

}; //namespace service
}; //namespace uxas

#endif /*DAIDALUS_WCV_Dection */


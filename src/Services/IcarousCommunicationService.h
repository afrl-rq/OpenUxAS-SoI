// ===============================================================================
// Authors: AFRL/RQQA & NASA/NIA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   IcarousCommunicationService.h
 * Authors: Paul Coen & Winston Smith
 *
 * Created on June 14, 2018, 3:55 PM
 * This file allows connectivity with the CRATOUS system
 * (CRoss Application Translator of Operational Unmanned Systems) 
 * CRATOUS allows cooperative mission planning between UxAS and ICAROUS
 *
 */

#ifndef UXAS_ICAROUSCOMMUNICATIONSERVICE_H
#define UXAS_ICAROUSCOMMUNICATIONSERVICE_H



#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "TypeDefs/UxAS_TypeDefs_Timer.h"




#include "ServiceBase.h"
#include "TypeDefs/UxAS_TypeDefs_String.h"
#include "CallbackTimer.h"


#include "afrl/cmasi/Waypoint.h"
#include "afrl/cmasi/TurnType.h"
#include "afrl/cmasi/MissionCommand.h"




#include <sys/types.h>
#include <sys/socket.h>
#include <stdio.h>
#include <string.h>
#include <netinet/in.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory>

#define PORT 5557

namespace uxas
{
namespace service
{

/*! \class IcarousCommunicationService
 *  \brief This service handles communication with ICAROUS for integration of the two pieces of software.
 *  
 * </ul> @n
 * 
 * Configuration String: <Service Type="IcarousCommunicationService" OptionString="Option_01" OptionInt="36" />
 * 
 * Options:
 *  - OptionString - sample string option
 *  - OptionInt - sample integer option
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::KeyValuePair
 * 
 * Sent Messages:
 *  - afrl::cmasi::KeyValuePair
 * 
 * 
 */

class IcarousCommunicationService : public ServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="IcarousCommunicationService". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("IcarousCommunicationService");
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
        return new IcarousCommunicationService;
    };

    IcarousCommunicationService();
    bool isInitializePlan(std::shared_ptr<afrl::cmasi::MissionCommand> & ptr_MissionCommand);

    virtual
    ~IcarousCommunicationService();

private:

    static
    ServiceBase::CreationRegistrar<IcarousCommunicationService> s_registrar;

    /** brief Copy construction not permitted */
    IcarousCommunicationService(IcarousCommunicationService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(IcarousCommunicationService const&) = delete;

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
    
    int client_sockfd;


private:
    // storage for the option entries
    std::string m_option01 = std::string("No Option 1");
    int32_t m_option02{0};
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_ICAROUSCOMMUNICATIONSERVICE_H */


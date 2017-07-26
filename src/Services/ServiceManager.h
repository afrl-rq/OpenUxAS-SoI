// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_SERVICE_SERVICE_MANAGER_H
#define UXAS_SERVICE_SERVICE_MANAGER_H

#include "ServiceBase.h"

#include "LmcpObjectMessageReceiverPipe.h"

#include <memory>
#include <mutex>
#include <unordered_map>
#include <vector>

namespace uxas
{
namespace service
{

/** \class ServiceManager
 * 
 * \par The <B><i>ServiceManager</i></B> is a singleton class that inherits from 
 * the <B><i>ServiceBase</i></B> class. It performs initial service creation 
 * for the UxAS entity at startup. After entity startup, it creates services 
 * per requests received from other services via messaging.  The 
 * <B><i>ServiceManager</i></B> exclusively uses the <B><i>ServiceBase</i></B> 
 * creation registry to create services.
 * 
 * @n
 */
class ServiceManager final : public ServiceBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("ServiceManager"); return (s_string); };

    static const std::string&
    s_directoryName() { static std::string s_string("svcmgr"); return (s_string); };

    static ServiceManager&
    getInstance();

    ~ServiceManager() { };

    void destroyServiceManager(){s_instance.reset();};
    
private:

    /** \brief Public, direct construction not permitted (singleton pattern) */
    ServiceManager()
    : ServiceBase(ServiceManager::s_typeName(), "") { };

    /** \brief Copy construction not permitted */
    ServiceManager(ServiceManager const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(ServiceManager const&) = delete;

    static std::unique_ptr<ServiceManager> s_instance;

public:

    /** \brief The <B><i>configureServiceManager</i></B> method must be invoked 
     * before calling the <B><i>initializeAndStart</i></B> method. 
     * It performs configuration specific to the ServiceManager and base class 
     * configuration. 
     * 
     * @return true if configuration succeeds; false if configuration fails.
     */
    bool
    configureServiceManager();
    
    /** \brief The <B><i>run</i></B> method must be invoked after first calling the 
     * <B><i>configureServiceManager</i></B> and <B><i>initializeAndStart</i></B> 
     * methods (in that order). It monitors and maintains services including 
     * resource de-allocation. It runs until application exit.
     * 
     */
    void
    run();
        
    /** \brief The <B><i>runUntil</i></B> method must be invoked after first calling the 
     * <B><i>configureServiceManager</i></B> and <B><i>initializeAndStart</i></B> 
     * methods (in that order). It monitors and maintains services including 
     * resource de-allocation. It runs until <b>duration_s</b> seconds have 
     * elapsed, then returns.
     * 
     * @param duration_s
     */
    void
    runUntil(uint32_t duration_s);
    
private:

    /** \brief The <B><i>initialize</i></B> method overrides a virtual method 
     * in base class <B><i>LmcpObjectNetworkClientBase</i></B>. It performs 
     * initial service creation at UxAS entity startup. 
     * 
     * @return true if initialize succeeds; false if initialize fails.
     */
    bool
    initialize() override;
   
    /**
     * \brief The <B><i>removeTerminatedServices</i></B> iterates through the 
     * service map and checks for terminated services.  The reference to each 
     * terminated service is removed from the service map (enabling object 
     * destruction).
     * 
     * @return number of running services.
     */
    uint32_t
    removeTerminatedServices();
        
    /**
     * \brief The <B><i>createService</i></B> method creates an instance of a UxAS service.
     * 
     * @param serviceXml XML string containing the service type and service 
     * configurations for service creation.
     * @return true if service was created; false if service creation failed.
     */
    bool
    createService(const std::string& serviceXml, int64_t newServiceId);

    /**
     * \brief The <B><i>createService</i></B> method creates an instance of a UxAS service.
     * 
     * @param xmlNode XML node containing the service type and service 
     * configurations for service creation.
     * @return true if service was created; false if service creation failed.
     */
    bool
    createService(const pugi::xml_node& serviceXmlNode, int64_t newServiceId);

public:
    
    /**
     * \brief The <B><i>createService</i></B> method creates an instance of a UxAS service.
     * 
     * @param xmlNode XML node containing the service type and service 
     * configurations for service creation.
     * @return true if service was created; false if service creation failed.
     */
    std::unordered_map<uint32_t, std::unique_ptr<ServiceBase>>
    createTestServices(const std::string& cfgXmlFilePath, uint32_t entityId, int64_t firstNetworkId);

    std::unordered_map<std::uint32_t, std::unique_ptr<uxas::service::ServiceBase>>& getServicesById(){return(m_servicesById);};

private:

    /**
     * \brief The <B><i>createService</i></B> method creates an instance of a UxAS service.
     * 
     * @param xmlNode XML node containing the service type and service 
     * configurations for service creation.
     * @return true if service was created; false if service creation failed.
     */
    std::unique_ptr<ServiceBase>
    instantiateConfigureInitializeStartService(const pugi::xml_node& serviceXmlNode, uint32_t entityId, int64_t networkId);

    /** \brief The <B><i>processReceivedLmcpMessage</i></B> method overrides a virtual method 
     * in base class <B><i>LmcpObjectNetworkClientBase</i></B> to process <b>LMCP</b> 
     * objects received via messaging.
     * 
     * @param receivedLmcpMessage received <b>LMCP</b> object.
     * @return true to terminate <B><i>ServiceManager</i></B>; false for 
     * <B><i>ServiceManager</i></B> to continue processing.
     */
    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

    void
    terminateAllServices();

    void
    shutdownProcessor();

    std::unordered_map<std::string,std::string> m_taskIdVsServiceId;
    std::mutex m_servicesByIdMutex;
    std::unordered_map<std::uint32_t, std::unique_ptr<uxas::service::ServiceBase>> m_servicesById;

    /** \brief  */
    bool m_isConfigured{false};
    
    std::atomic<bool> m_isServiceManagerTermination{false};

};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_SERVICE_MANAGER_H */

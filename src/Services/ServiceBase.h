// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_SERVICE_SERVICE_BASE_H
#define UXAS_SERVICE_SERVICE_BASE_H

#include "LmcpObjectNetworkClientBase.h"

#include "UxAS_Log.h"

namespace uxas
{
namespace service
{

/** \class ServiceBase
 * 
 * \par The <B><i>ServiceBase</i></B> is the base class for all UxAS service classes. 
 * Service class constructors are registered in the <B><i>ServiceBase</i></B> 
 * creation registry.
 * 
 * @n
 */
class ServiceBase : public uxas::communications::LmcpObjectNetworkClientBase
{
public:

    ServiceBase(const std::string& serviceType, const std::string& workDirectoryName);

    virtual
    ~ServiceBase();

private:

    /** \brief Copy construction not permitted */
    ServiceBase(ServiceBase const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(ServiceBase const&) = delete;

public:

    /** \brief The <B><i>configureService</i></B> method performs service configuration. 
     * It must be invoked before calling the <B><i>initializeAndStartService</i></B>. 
     * 
     * @param parentOfWorkDirectory parent directory where work directory will be created
     * @param serviceXml XML configuration
     * @return true if configuration succeeds; false if configuration fails.
     */
    bool
    configureService(const std::string& parentOfWorkDirectory, const std::string& serviceXml);

    /** \brief The <B><i>configureService</i></B> method performs service configuration. 
     * It must be invoked before calling the <B><i>initializeAndStartService</i></B>. 
     * 
     * @param parentOfWorkDirectory parent directory where work directory will be created
     * @param serviceXmlNode XML configuration
     * @return true if configuration succeeds; false if configuration fails.
     */
    bool
    configureService(const std::string& parentWorkDirectory, const pugi::xml_node& serviceXmlNode);

    /** \brief The <B><i>initializeAndStartService</i></B> method performs service 
     * initialization and startup. It must be invoked after calling the 
     * <B><i>configureService</i></B> method. Do not use for 
     * <B><i>ServiceManager</i></B>, instead invoke the 
     * <B><i>initializeAndStart</i></B> method.
     * 
     * @return true if all initialization and startup succeeds; false if initialization or startup fails.
     */
    bool
    initializeAndStartService();

    /**
     * \brief The <B><i>getUniqueNetworkClientId</i></B> returns a unique service ID. 
     * It returns the ID from a call to getUniqueNetworkClientId(), which are used as service IDs
     * 
     * @return unique service ID.
     */
    static int64_t
    getUniqueServceId()
    {
        return (getUniqueNetworkClientId());
    };
    
public:

    /** \brief unique ID of the component.  */
    std::uint32_t m_serviceId;

    /** \brief  */
    std::string m_serviceType;

    /** \brief  */
    std::string m_workDirectoryName;

protected:

    /** \brief  */
    bool m_isConfigured{false};

    /** \brief  */
    std::string m_workDirectoryPath;
        
    uxas::communications::LmcpObjectNetworkClientBase::ReceiveProcessingType m_receiveProcessingType{uxas::communications::LmcpObjectNetworkClientBase::ReceiveProcessingType::LMCP};

    // <editor-fold defaultstate="collapsed" desc="Static Service Registry">    
public:

    /** \brief The <B><i>instantiateService</i></B> method creates an instance 
     * of a service class that inherits from <B><i>ServiceBase</i></B>
     * 
     * @param serviceType type name of the service to be instantiated
     * @return instantiated service
     */
    static
    std::unique_ptr<ServiceBase>
    instantiateService(const std::string& serviceType)
    {
        auto it = createFunctionByServiceType().find(serviceType);
        ServiceBase * newService(it == createFunctionByServiceType().end() ? nullptr : (it->second)());
        std::unique_ptr<ServiceBase> service(newService);
        return (service);
    };

protected:

    /** \brief type representing a pointer to a service creation function.  */
    using serviceCreationFunctionPointer = ServiceBase* (*)();

    /** \brief static service creation function implemented that is implemented by subclasses.  */
    static
    ServiceBase*
    create() { return nullptr; };

    /** \brief registers service type name, alias type names and it's create() function for a subclass.  */
    static
    void
    registerServiceCreationFunctionPointers(const std::vector<std::string>& registryServiceTypeNames, serviceCreationFunctionPointer functionPointer)
    {
        for (auto& serviceTypeName : registryServiceTypeNames)
        {
            auto it = createFunctionByServiceType().find(serviceTypeName);
            if (it != createFunctionByServiceType().end())
            {
                UXAS_LOG_WARN("ServiceBase::registerServiceCreationFunctionPointers is overwriting existing service creation function pointer ", serviceTypeName);
            }
            createFunctionByServiceType()[serviceTypeName] = functionPointer;
        }
    };

    template <typename T>
    struct CreationRegistrar
    {
        explicit
        CreationRegistrar(const std::vector<std::string>& registryServiceTypeNames)
        {
            ServiceBase::registerServiceCreationFunctionPointers(registryServiceTypeNames, &T::create);
        }
    };

private:

    /** \brief function to access static map of create functions keyed by serviceType.
     * 
     * @return service type to create function map.
     */
    static
    std::unordered_map<std::string, ServiceBase::serviceCreationFunctionPointer>&
    createFunctionByServiceType()
    {
        static std::unordered_map<std::string, ServiceBase::serviceCreationFunctionPointer> createFncPtrMap;
        return createFncPtrMap;
    }

    // </editor-fold>
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_SERVICE_BASE_H */

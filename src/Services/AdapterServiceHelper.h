// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_SERVICE_ADAPTER_ADAPTER_SERVICE_HELPER_H
#define UXAS_SERVICE_ADAPTER_ADAPTER_SERVICE_HELPER_H

#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/KeyValuePair.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/ServiceStatus.h"

#include "../../common/log/Log.h"

#include "../../stduxas/stdUniquePtr.h"

namespace uxas
{
namespace service
{
namespace adapter
{

enum class SerialConnectionAction
{
    READ,
    WRITE
};

/** \class AdapterServiceHelper
 * 
 * 
 * \par Description:
 * 
 * \n
 */
class AdapterServiceHelper
{
public:

//    static AdapterServiceHelper&
//    getInstance();

    static
    std::unique_ptr<avtas::lmcp::Object>
    createLmcpMessageObjectSerialConnectionFailure(
                const std::string& serviceType, SerialConnectionAction actionType, 
                const std::string& ttyDevice, const std::exception& exception, std::string& errorMessage)
    {
        std::string actionString;
        switch (actionType)
        {
            case SerialConnectionAction::READ:
                actionString = "read";
                break;
            case SerialConnectionAction::WRITE:
                actionString = "write";
                break;
        }
        
        errorMessage = serviceType + ": Error on serial port " 
                + ttyDevice + " during " + actionString + " operation";
        std::unique_ptr<afrl::cmasi::ServiceStatus> serviceStatus = uxas::stduxas::make_unique<afrl::cmasi::ServiceStatus>();
        std::unique_ptr<afrl::cmasi::KeyValuePair> keyValuePair = uxas::stduxas::make_unique<afrl::cmasi::KeyValuePair>();
        keyValuePair->setKey(std::string("EXCEPTION " + serviceType));
        keyValuePair->setValue(errorMessage);
        serviceStatus->getInfo().push_back(keyValuePair.get());
        std::unique_ptr<avtas::lmcp::Object> lmcpObject;
        lmcpObject.reset(static_cast<avtas::lmcp::Object*> (serviceStatus.get()));
        return (lmcpObject);
    };
    
private:

    // \brief Prevent direct, public construction (singleton pattern)
    AdapterServiceHelper() { };

    // \brief Prevent copy construction
    AdapterServiceHelper(AdapterServiceHelper const&) = delete;

    // \brief Prevent copy assignment operation
    void operator=(AdapterServiceHelper const&) = delete;

//    static std::unique_ptr<AdapterServiceHelper> s_instance;
    
};

}; //namespace adapter
}; //namespace service
}; //namespace uxas

#endif	/* UXAS_SERVICE_ADAPTER_ADAPTER_SERVICE_HELPER_H */

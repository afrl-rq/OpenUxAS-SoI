// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_DATA_SERIAL_HELPER_H
#define UXAS_MESSAGE_DATA_SERIAL_HELPER_H

#include "afrl/cmasi/KeyValuePair.h"
#include "afrl/cmasi/ServiceStatus.h"

#include "stdUniquePtr.h"

#include <sstream>

namespace uxas
{
namespace communications
{
namespace data
{

/** \class SerialConnectionAction
 * (enum SerialConnectionAction)
 * 
 * \par Description:
 * 
 * \n
 */
enum class SerialConnectionAction
{
    READ,
    WRITE
};

class SerialHelper
{
public:

    static
    std::unique_ptr<avtas::lmcp::Object>
    createLmcpMessageObjectSerialConnectionFailure(
                const std::string& networkActorType, SerialConnectionAction actionType, 
                const std::string& serialPortAddress, uint32_t baudRate, const std::exception& exception, std::string& errorMessage)
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
        
        std::ostringstream ss;
        ss << networkActorType << " - Error on serial port " << serialPortAddress
        		<< " with baud rate " << baudRate
				<< " during " << actionString << " operation";
        errorMessage = ss.str();
        std::unique_ptr<afrl::cmasi::ServiceStatus> serviceStatus = uxas::stduxas::make_unique<afrl::cmasi::ServiceStatus>();
        std::unique_ptr<afrl::cmasi::KeyValuePair> keyValuePair = uxas::stduxas::make_unique<afrl::cmasi::KeyValuePair>();
        keyValuePair->setKey(std::string("EXCEPTION " + networkActorType));
        keyValuePair->setValue(errorMessage);
        serviceStatus->getInfo().push_back(keyValuePair.get());
        serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::ServiceStatusType::Error);
        std::unique_ptr<avtas::lmcp::Object> lmcpObject(serviceStatus.get());
        return (lmcpObject);
    };

private:

    // \brief Prevent direct, public construction (singleton pattern)
    SerialHelper() { };

    /** \brief Copy construction not permitted */
    SerialHelper(SerialHelper const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(SerialHelper const&) = delete;

};

}; //namespace data
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_DATA_SERIAL_HELPER_H */

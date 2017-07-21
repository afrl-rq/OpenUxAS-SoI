// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
 * File:   HelloRust.h
 * Author: acfoltzer
 */

#ifndef UXAS_HELLO_RUST_H
#define UXAS_HELLO_RUST_H


#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "TypeDefs/UxAS_TypeDefs_Timer.h"

namespace uxas
{
namespace service
{

/*! \class HelloRust
 *\brief This is a basic example of a UxAS service that sends/receives KeyValuePair
 * messages and prints out the results.
 *
 * Configuration String:
 *  <Service Type="HelloRust" StringToSend="Hello Rust!" SendPeriod_ms="1000" />
 *
 * Options:
 *  - StringToSend - the text of the message to send out
 *  - SendPeriod_ms - how often, in milliseconds, to send the message
 *
 * Subscribed Messages:
 *  - afrl::cmasi::KeyValuePair
 *
 * Sent Messages:
 *  - afrl::cmasi::KeyValuePair
 *
 */

class HelloRust : public ServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="HelloRust". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("HelloRust");
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
        return new HelloRust;
    };

    HelloRust();

    virtual
    ~HelloRust();

private:

    static
    ServiceBase::CreationRegistrar<HelloRust> s_registrar;

    /** brief Copy construction not permitted */
    HelloRust(HelloRust const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(HelloRust const&) = delete;

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
    /** brief The timer calls this function periodically to send out messages */
    void OnSendMessage();

private:
    std::string m_stringToSend = std::string("Hello Rust!");
    int64_t m_sendPeriod_ms{1000};
    uint64_t m_sendMessageTimerId{0};

};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_HELLO_RUST_H */


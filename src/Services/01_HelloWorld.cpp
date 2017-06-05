// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   HelloWorld.cpp
 * Author: steve
 *
 * Created on March 17, 2017, 5:55 PM
 *
 * <Service Type="HelloWorld" StringToSend="Option_01" SendPeriod_ms="36" />
 * 
 */

// include header for this service
#include "01_HelloWorld.h"

// include to add a periodic timer to send out messages periodically
#include "UxAS_TimerManager.h"

//include for KeyValuePair LMCP Message
#include "afrl/cmasi/KeyValuePair.h"

// print outs
#include <iostream>     // std::cout, cerr, etc

// convenience definitions for the option strings
#define STRING_XML_STRING_TO_SEND "StringToSend"
#define STRING_XML_SEND_PERIOD_MS "SendPeriod_ms"

// namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{

// this entry registers the service in the service creation registry
HelloWorld::ServiceBase::CreationRegistrar<HelloWorld>
HelloWorld::s_registrar(HelloWorld::s_registryServiceTypeNames());

// service constructor
HelloWorld::HelloWorld()
: ServiceBase(HelloWorld::s_typeName(), HelloWorld::s_directoryName()) { };

// service destructor
HelloWorld::~HelloWorld() { };


bool HelloWorld::configure(const pugi::xml_node& ndComponent)
{
    bool isSuccess(true);

    // process options from the XML configuration node:
    if (!ndComponent.attribute(STRING_XML_STRING_TO_SEND).empty())
    {
        m_stringToSend = ndComponent.attribute(STRING_XML_STRING_TO_SEND).value();
    }
    if (!ndComponent.attribute(STRING_XML_SEND_PERIOD_MS).empty())
    {
        m_sendPeriod_ms = ndComponent.attribute(STRING_XML_SEND_PERIOD_MS).as_int64();
    }

    // subscribe to messages::
    addSubscriptionAddress(afrl::cmasi::KeyValuePair::Subscription);

    return (isSuccess);
}

bool HelloWorld::initialize()
{
    // create send timer
    m_sendMessageTimerId = uxas::common::TimerManager::getInstance().createTimer(
        std::bind(&HelloWorld::OnSendMessage, this), "HelloWorld::OnSendMessage");
    
    return (true);
}

bool HelloWorld::start()
{
    // start the timer
    return (uxas::common::TimerManager::getInstance().startPeriodicTimer(m_sendMessageTimerId,0,m_sendPeriod_ms));
};

bool HelloWorld::terminate()
{
    // kill the timer
    uint64_t delayTime_ms{1000};
    if (m_sendMessageTimerId && !uxas::common::TimerManager::getInstance().destroyTimer(m_sendMessageTimerId, delayTime_ms))
    {
        UXAS_LOG_WARN(s_typeName(), "::HelloWorld::terminate() failed to destroy message send timer ",
                 "with timer ID ", m_sendMessageTimerId, " within ", delayTime_ms, " millisecond timeout");
    }
    
    return (true);
}

bool HelloWorld::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    if (afrl::cmasi::isKeyValuePair(receivedLmcpMessage->m_object))
    {
        //receive message
        auto keyValuePairIn = std::static_pointer_cast<afrl::cmasi::KeyValuePair> (receivedLmcpMessage->m_object);
        std::cout << "*** RECEIVED:: Received Id[" << m_serviceId << "] Sent Id[" << keyValuePairIn->getKey() << "] Message[" << keyValuePairIn->getValue() << "] *** " << std::endl;
    }
    return false;
}

void HelloWorld::OnSendMessage()
{
    // send out the message
    auto keyValuePairOut = std::make_shared<afrl::cmasi::KeyValuePair>();
    keyValuePairOut->setKey(std::to_string(m_serviceId));
    keyValuePairOut->setValue(m_stringToSend);
    sendSharedLmcpObjectBroadcastMessage(keyValuePairOut);
    //std::cout << "*** SENT:: Service Id[" << m_serviceId << "] Sent a KeyValuePair with the Key[" << keyValuePairOut->getKey() << "] and Value[" << keyValuePairOut->getValue() << "] *** " << std::endl;
    
    // reset the timer
}


}; //namespace service
}; //namespace uxas

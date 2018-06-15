// ===============================================================================
// Authors: AFRL/RQQA & NASA/NIA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   IcarousCommunicationService.cpp
 * Author: Paul Coen & Winston Smith
 *
 * Created on March 17, 2017, 5:55 PM
 *
 * <Service Type="IcarousCommunicationService" OptionString="Option_01" OptionInt="36" />
 * 
 * This file is meant to connect to the cFS module called CRATOUS in the ICAROUS system
 * (CRoss Application Translator of Operational Unmanned Systems) 
 * 
 */

// include header for this service
#include "IcarousCommunicationService.h"

//include for KeyValuePair LMCP Message
#include "afrl/cmasi/KeyValuePair.h"


#include <iostream>     // std::cout, cerr, etc

// convenience definitions for the option strings
#define STRING_XML_OPTION_STRING "OptionString"
#define STRING_XML_OPTION_INT "OptionInt"

// namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{

// this entry registers the service in the service creation registry
IcarousCommunicationService::ServiceBase::CreationRegistrar<IcarousCommunicationService>
IcarousCommunicationService::s_registrar(IcarousCommunicationService::s_registryServiceTypeNames());

// service constructor
IcarousCommunicationService::IcarousCommunicationService()
: ServiceBase(IcarousCommunicationService::s_typeName(), IcarousCommunicationService::s_directoryName()) { };

// service destructor
IcarousCommunicationService::~IcarousCommunicationService() { };


bool IcarousCommunicationService::configure(const pugi::xml_node& ndComponent)
{
    bool isSuccess(true);

    // process options from the XML configuration node:
    if (!ndComponent.attribute(STRING_XML_OPTION_STRING).empty())
    {
        m_option01 = ndComponent.attribute(STRING_XML_OPTION_STRING).value();
    }
    if (!ndComponent.attribute(STRING_XML_OPTION_INT).empty())
    {
        m_option02 = ndComponent.attribute(STRING_XML_OPTION_INT).as_int();
    }

    // subscribe to messages::
    addSubscriptionAddress(afrl::cmasi::KeyValuePair::Subscription);

    return (isSuccess);
}

bool IcarousCommunicationService::initialize()
{
    // perform any required initialization before the service is started
    std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

bool IcarousCommunicationService::start()
{
    // perform any actions required at the time the service starts
    std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
        
    //START ADDED CODE
    const char *protocol1 = "ICAROUS-UxAS_LMCP";
    const char *protocol2 = "ok ";
    const char *sharedSecret = "28a4b77b86aa32715e4c271415b28447b8c08d704fd9ffb1258bced7b7167fe0";
    const char *err = "error";
    
    
    
    socklen_t server_len;
    struct sockaddr_in server_address;
    int server_sockfd = -2;
    server_sockfd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if(server_sockfd <= 0){
      fprintf(stderr, "Fatal error, socket could not be made!\n");
      return (false);
    }
    int i = 1;
    if((setsockopt(server_sockfd, SOL_SOCKET, SO_REUSEADDR, &i, sizeof(i))) == -1){
      fprintf(stderr, "Fatal error, socket could not be set up!\n");
      return (false);
    }
    server_address.sin_family = AF_INET;
    server_address.sin_addr.s_addr = htonl(INADDR_ANY);
    server_address.sin_port = htons(PORT);
    server_len = sizeof(server_address);
    if((bind(server_sockfd, (struct sockaddr *)&server_address, server_len)) == -1){
      fprintf(stderr, "Fatal error, socket could not be bound!\n");
      return (false);
    }

    listen(server_sockfd, 1);
    int client_sockfd = accept(server_sockfd, NULL, NULL);
    if((write(client_sockfd, protocol1, strlen(protocol1))) <= 0){
        fprintf(stderr, "Fatal error, write communication protocol name failed!\n");
        close(client_sockfd);
        return (false);
    }

    int nread;
    char buffer[strlen(sharedSecret) + 1];
    buffer[strlen(sharedSecret)] = '\0';
    if((nread = read(client_sockfd, buffer, strlen(sharedSecret))) <= 0){
        fprintf(stderr, "Fatal error, could not read ICAROUS password!\n");
        close(client_sockfd);
        return (false);
    }
    else if(!strcmp(buffer, sharedSecret)){ //!strcmp==true indicates the strings are the same
        if((write(client_sockfd, protocol2, strlen(protocol2))) <= 0){
            fprintf(stderr, "Fatal error, write confirmation to ICAROUS failed!\n");
            close(client_sockfd);
            return (false);
        }

        //Begin communication protocol
        fprintf(stdout, "ICAROUS has connected to UxAS!\n");

        //communication code goes here
        
        char inputBuff[4097];
        inputBuff[4096] = '\0';
        read(client_sockfd, inputBuff, strlen("Hello World ICAROUS 2"));
        fprintf(stdout, "%s\n", inputBuff);

        write(client_sockfd, "Hello World UxAS 2", strlen("Hello World UxAS 2"));
        
    }
    else{
        write(client_sockfd, err, strlen(err));
        close(client_sockfd);
        return (false);
    }
    
    //std::cout << "ICAROUS has dissconnected unexpectedly" << std::endl;
    return (true);
};

bool IcarousCommunicationService::terminate()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}
    
bool IcarousCommunicationService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    if (afrl::cmasi::isKeyValuePair(receivedLmcpMessage->m_object))
    {
        //receive message
        auto keyValuePairIn = std::static_pointer_cast<afrl::cmasi::KeyValuePair> (receivedLmcpMessage->m_object);
        std::cout << "*** RECEIVED:: Service[" << s_typeName() << "] Received a KeyValuePair with the Key[" << keyValuePairIn->getKey() << "] and Value[" << keyValuePairIn->getValue() << "] *** " << std::endl;
        
        // send out response
        auto keyValuePairOut = std::make_shared<afrl::cmasi::KeyValuePair>();
        keyValuePairOut->setKey(s_typeName());
        keyValuePairOut->setValue(std::to_string(m_serviceId));
        sendSharedLmcpObjectBroadcastMessage(keyValuePairOut);
        
    }
    return false;
}

}; //namespace service
}; //namespace uxas

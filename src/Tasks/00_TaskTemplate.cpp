// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   00_TaskTemplate.cpp
 * Author: steve
 *
 * Created on March 22, 2017, 5:55 PM
 *
 * <Service Type="TaskTemplate" OptionString="Option_01" OptionInt="36" />
 * 
 */

// include header for this service
#include "00_TaskTemplate.h"

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
namespace task
{

// this entry registers the service in the service creation registry
TaskTemplate::ServiceBase::CreationRegistrar<TaskTemplate>
TaskTemplate::s_registrar(TaskTemplate::s_registryServiceTypeNames());

// service constructor
TaskTemplate::TaskTemplate()
: TaskServiceBase(TaskTemplate::s_typeName(), TaskTemplate::s_directoryName()) { };

TaskTemplate::~TaskTemplate()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::~TaskTemplate()");
};


bool
TaskTemplate::configureTask(const pugi::xml_node& ndComponent)

{
    bool isSuccess(true);

//        if (uxas::project::pisr::isPISR_Task(m_task.get()))
//        {
//            m_pisrTask = std::static_pointer_cast<uxas::project::pisr::PISR_Task>(m_task);
//            if (!m_pisrTask)
//            {
//                sstrErrors << "ERROR:: **TaskTemplate::bConfigure failed to cast a PISR_Task from the task pointer." << std::endl;
//                isSuccessful = false;
//            }
//            else
//            {
//                //////////////////////////////////////////////
//                //////////// PROCESS OPTIONS /////////////////
//                pugi::xml_node ndTaskOptions = ndComponent.child(m_taskOptions_XmlTag.c_str());
//                if (ndTaskOptions)
//                {
//                    for (pugi::xml_node ndTaskOption = ndTaskOptions.first_child(); ndTaskOption; ndTaskOption = ndTaskOption.next_sibling())
//                    {
//                        
////        m_option01 = ndComponent.attribute(STRING_XML_OPTION_STRING).value();
////        m_option02 = ndComponent.attribute(STRING_XML_OPTION_INT).as_int();
//                        
//                        
//                        if (std::string(STRING_XML_USE_ASSIGNED_TASK_ID) == ndTaskOption.name())
//                        {
//                            m_useAssignedTaskId = true;
//                        }
//                    }
//                }
//            }
//        }
//        else
//        {
//            sstrErrors << "ERROR:: **TaskTemplate::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a TaskTemplate_Task." << std::endl;
//            isSuccessful = false;
//        }

    // subscribe to messages::
    addSubscriptionAddress(afrl::cmasi::KeyValuePair::Subscription);

    return (isSuccess);
}

bool TaskTemplate::initializeTask()
{
    // perform any required initialization before the service is started
    std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

bool TaskTemplate::startTask()
{
    // perform any actions required at the time the service starts
    std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
};

bool TaskTemplate::terminateTask()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

bool TaskTemplate::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
{
//    if (afrl::cmasi::isKeyValuePair(receivedLmcpObject))
//    {
//        //receive message
//        auto keyValuePairIn = std::static_pointer_cast<afrl::cmasi::KeyValuePair> (receivedLmcpMessage->m_object);
//        std::cout << "*** RECEIVED:: Service[" << s_typeName() << "] Received a KeyValuePair with the Key[" << keyValuePairIn->getKey() << "] and Value[" << keyValuePairIn->getValue() << "] *** " << std::endl;
//        
//        // send out response
//        auto keyValuePairOut = std::make_shared<afrl::cmasi::KeyValuePair>();
//        keyValuePairOut->setKey(s_typeName());
//        keyValuePairOut->setValue(std::to_string(m_serviceId));
//        sendSharedLmcpObjectBroadcastMessage(keyValuePairOut);
//        
//    }
    return false;
}

}; //namespace task
}; //namespace service
}; //namespace uxas

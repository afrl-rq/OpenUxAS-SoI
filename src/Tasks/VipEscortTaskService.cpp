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
 * <Service Type="VipEscortTaskService" OptionString="Option_01" OptionInt="36" />
 * 
 */
#include "VipEscortTaskService.h"
// include header for this service


//include for KeyValuePair LMCP Message
#include "afrl/cmasi/KeyValuePair.h"

#include "uxas/UT/VipEscortTask.h"
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
VipEscortTaskService::ServiceBase::CreationRegistrar<VipEscortTaskService>
VipEscortTaskService::s_registrar(VipEscortTaskService::s_registryServiceTypeNames());

// service constructor
VipEscortTaskService::VipEscortTaskService()
: TaskServiceBase(VipEscortTaskService::s_typeName(), VipEscortTaskService::s_directoryName()) { };

VipEscortTaskService::~VipEscortTaskService()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::~VipEscortTaskService()");
};


bool
VipEscortTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    bool isSuccess(true);
    std::shared_ptr<uxas::UT::VipEscortTask> m_VipEscortTask;
    std::stringstream sstrErrors;
       if (uxas::UT::isVipEscortTask(m_task.get()))
       {
           m_VipEscortTask = std::static_pointer_cast<uxas::UT::VipEscortTask>(m_task);
           if (!m_VipEscortTask)
           {
               sstrErrors << "ERROR:: **VipEscortTaskService::bConfigure failed to cast a VipEscort_Task from the task pointer." << std::endl;
               isSuccess = false;
           }
       }
       else
       {
           sstrErrors << "ERROR:: **VipEscortTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a VipEscortTaskService." << std::endl;
           isSuccess = false;
       }

    addSubscriptionAddress(afrl::cmasi::KeyValuePair::Subscription);

    return (isSuccess);
}

void VipEscortTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

    int64_t optionId(1);
    int64_t taskId(m_VipEscortTask->getTaskID());

    if (isCalculateOption(taskId, optionId, m_VipEscortTask->getEligibleEntities()))
    {
        optionId++;
    }

    std::string compositionString("+(");
    for (auto itOption = m_taskPlanOptions->getOptions().begin(); itOption != m_taskPlanOptions->getOptions().end(); itOption++)
    {
        compositionString += "p";
        compositionString += std::to_string((*itOption)->getOptionID());
        compositionString += " ";
    }
    compositionString += ")";
    std::cout << compositionString << std::endl;
    
    m_taskPlanOptions->setComposition(compositionString);

    // send out the options
    if (isSuccessful)
    {
        auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
        sendSharedLmcpObjectBroadcastMessage(newResponse);
    }
};

bool VipEscortTaskService::isCalculateOption(const int64_t& taskId, int64_t& optionId, const std::vector<int64_t>& eligibleEntities) {
    bool isSuccessful{true};

    // if (m_watchedEntityStateLast)
    // {
    //     auto taskOption = new uxas::messages::task::TaskOption;
    //     taskOption->setTaskID(taskId);
    //     taskOption->setOptionID(optionId);
    //     taskOption->getEligibleEntities() = eligibleEntities;
    //     taskOption->setStartLocation(m_watchedEntityStateLast->getLocation()->clone());
    //     taskOption->setStartHeading(m_watchedEntityStateLast->getHeading());
    //     taskOption->setEndLocation(m_watchedEntityStateLast->getLocation()->clone());
    //     taskOption->setEndHeading(m_watchedEntityStateLast->getHeading());
    //     auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
    //     m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
    //     m_taskPlanOptions->getOptions().push_back(taskOption);
    //     taskOption = nullptr; //just gave up ownership

    // }
    // else
    // {
    //     CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no watchedEntityState found for Entity[" << m_watchTask->getWatchedEntityID() << "]")
    //     isSuccessful = false;
    // }

    return (isSuccessful);
}

bool VipEscortTaskService::initializeTask()
{
    // perform any required initialization before the service is started
    std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

bool VipEscortTaskService::startTask()
{
    // perform any actions required at the time the service starts
    std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
};

bool VipEscortTaskService::terminateTask()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

bool VipEscortTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
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

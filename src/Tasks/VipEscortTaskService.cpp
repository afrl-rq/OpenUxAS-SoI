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
#include "afrl/cmasi/LoiterTask.h"
#include "afrl/cmasi/Location3D.h"
#include "avtas/lmcp/LmcpXMLReader.h"
#include "uxas/UT/VipEscortTask.h"
#include <iostream>     // std::cout, cerr, etc

// convenience definitions for the option strings
#define STRING_XML_OPTION_STRING "OptionString"
#define STRING_XML_OPTION_INT "OptionInt"
#define STRING_XML_ENTITY_STATES "EntityStates"
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
    bool isSuccessful(true);
    std::stringstream sstrErrors;
       if (uxas::UT::isVipEscortTask(m_task.get()))
       {
           m_VipEscortTask = std::static_pointer_cast<uxas::UT::VipEscortTask>(m_task);
           if (!m_VipEscortTask)
           {
               sstrErrors << "ERROR:: **VipEscortTaskService::bConfigure failed to cast a VipEscort_Task from the task pointer." << std::endl;
               isSuccessful = false;
           }
       }
       else
       {
           sstrErrors << "ERROR:: **VipEscortTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a VipEscortTaskService." << std::endl;
           isSuccessful = false;
       }

    if (isSuccessful)
    {
            pugi::xml_node entityStates = ndComponent.child(STRING_XML_ENTITY_STATES);
            if (entityStates)
            {
                for (auto ndEntityState = entityStates.first_child(); ndEntityState; ndEntityState = ndEntityState.next_sibling())
                {

                    std::shared_ptr<afrl::cmasi::AirVehicleState> entityState;
                    std::stringstream stringStream;
                    ndEntityState.print(stringStream);
                    avtas::lmcp::Object* object = avtas::lmcp::xml::readXML(stringStream.str());
                    if (object != nullptr)
                    {
                        entityState.reset(static_cast<afrl::cmasi::AirVehicleState*> (object));
                        object = nullptr;
                        m_AirVehicleState = entityState;
                    }
                }
            }

    } //if(isSuccessful)
    return (isSuccessful);

    addSubscriptionAddress(afrl::cmasi::KeyValuePair::Subscription);

    return (isSuccessful);
}

void VipEscortTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

    int64_t optionId(1);

    int64_t vip = m_VipEscortTask->getVIP();
    int64_t uav1 = m_VipEscortTask->getUAV1();
    int64_t uav2 = m_VipEscortTask->getUAV2();

    auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
    auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
    pTaskOptionClass->m_taskOption->setTaskID(m_task->getTaskID());
    pTaskOptionClass->m_taskOption->setOptionID(optionId);
    pTaskOptionClass->m_taskOption->getEligibleEntities().push_back(vip);
    pTaskOptionClass->m_taskOption->setStartLocation(m_AirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setStartHeading(0);
    pTaskOptionClass->m_taskOption->setEndLocation(m_AirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setEndHeading(0);
    m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
    m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());

    // setting task option for UAV1
    optionId++;
    pTaskOptionClass->m_taskOption->setOptionID(optionId);
    pTaskOptionClass->m_taskOption->getEligibleEntities().clear();
    pTaskOptionClass->m_taskOption->getEligibleEntities().push_back(uav1);
    pTaskOptionClass->m_taskOption->setStartLocation(m_AirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setStartHeading(0);
    pTaskOptionClass->m_taskOption->setEndLocation(m_AirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setEndHeading(0);
    m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
    m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());   

    // setting task option for UAV2
    // optionId++;
    // pTaskOptionClass->m_taskOption->setOptionID(optionId);
    // pTaskOptionClass->m_taskOption->getEligibleEntities().push_back(uav2);
    // m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
    // m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());  

    std::string compositionString("|(");
    compositionString += "p1 p2)";

    std::cout << compositionString << std::endl;
    
    m_taskPlanOptions->setComposition(compositionString);

    // send out the options
    if (isSuccessful)
    {
        auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
        sendSharedLmcpObjectBroadcastMessage(newResponse);
        std::cout << "**VipEscortTaskService::Message sent!" << std::endl;
    }
};

bool VipEscortTaskService::isCalculateOption(const int64_t& taskId, int64_t& optionId, const std::vector<int64_t>& eligibleEntities) {
    bool isSuccessful{true};


    // auto taskOption = new uxas::messages::task::TaskOption;
    // taskOption->getEligibleEntities().push_back(optionId);
    // taskOption->setTaskID(taskId);
    // taskOption->setOptionID(optionId);
    // taskOption->getEligibleEntities() = eligibleEntities;
    // taskOption->setStartLocation(m_watchedEntityStateLast->getLocation()->clone());
    // taskOption->setStartHeading(m_watchedEntityStateLast->getHeading());
    // taskOption->setEndLocation(m_watchedEntityStateLast->getLocation()->clone());
    // taskOption->setEndHeading(m_watchedEntityStateLast->getHeading());
    // auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
    // m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
    // m_taskPlanOptions->getOptions().push_back(taskOption);
    // taskOption = nullptr; //just gave up ownership


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
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    auto airVehicleState = std::dynamic_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpObject);
    if (airVehicleState)
    {
        m_AirVehicleState = airVehicleState;
    }
    return (false); // always false implies never terminating service from here
};

}; //namespace task
}; //namespace service
}; //namespace uxas

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
#include "afrl/cmasi/Location3D.h"
#include "avtas/lmcp/LmcpXMLReader.h"
#include <Python.h>
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

    // setenv("PYTHONPATH", ".", 1);

    // Py_Initialize();

    // PyObject* module = PyImport_ImportModule("mymath");
    // assert(module != NULL);

    // PyObject* klass = PyObject_GetAttrString(module, "math");
    // assert(klass != NULL);

    // PyObject* controller = PyInstance_New(klass, NULL, NULL);
    // assert(controller != NULL);

    // PyObject* result = PyObject_CallMethod(controller, "add", "(ii)", 1, 2);
    // assert(result != NULL);

    // printf("1 + 2 = %ld\n", PyInt_AsLong(result));




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
                        if (entityState->getID() == m_VipEscortTask->getVIP())
                        {
                            m_VipAirVehicleState = entityState;
                        }
                        else if (entityState->getID() == m_VipEscortTask->getUAV1())
                        {
                            m_Uav1AirVehicleState = entityState;
                        }
                        else if (entityState->getID() == m_VipEscortTask->getUAV2())
                        {
                            m_Uav2AirVehicleState = entityState;
                        }                        
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

    // int64_t optionId(1);

    int64_t vip = m_VipEscortTask->getVIP();
    int64_t uav1 = m_VipEscortTask->getUAV1();
    int64_t uav2 = m_VipEscortTask->getUAV2();


    auto taskOption = new uxas::messages::task::TaskOption;
    taskOption->setTaskID(m_task->getTaskID());
    taskOption->setOptionID(vip);
    taskOption->getEligibleEntities().clear();
    taskOption->getEligibleEntities().push_back(vip); // defaults to all entities eligible
    auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
    auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);

    // auto pTaskOption = std::make_shared<uxas::messages::task::TaskOption>();
    // auto pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
    // pTaskOptionClass->m_taskOption->setTaskID(m_task->getTaskID());
    // pTaskOptionClass->m_taskOption->setOptionID(vip);
    // pTaskOptionClass->m_taskOption->getEligibleEntities().push_back(vip);
    pTaskOptionClass->m_taskOption->setStartLocation(m_VipAirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setStartHeading(0);
    pTaskOptionClass->m_taskOption->setEndLocation(m_VipAirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setEndHeading(0);
    m_optionIdVsTaskOptionClass.insert(std::make_pair(vip, pTaskOptionClass));
    m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());

    // setting task option for UAV1
    taskOption = new uxas::messages::task::TaskOption;
    taskOption->setTaskID(m_task->getTaskID());
    taskOption->setOptionID(uav1);
    taskOption->getEligibleEntities().clear();
    taskOption->getEligibleEntities().push_back(uav1); // defaults to all entities eligible
    pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
    pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);

    // pTaskOptionClass->m_taskOption->setOptionID(uav1);
    // pTaskOptionClass->m_taskOption->getEligibleEntities().clear();
    // pTaskOptionClass->m_taskOption->getEligibleEntities().push_back(uav1);
    pTaskOptionClass->m_taskOption->setStartLocation(m_Uav1AirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setStartHeading(0);
    pTaskOptionClass->m_taskOption->setEndLocation(m_Uav1AirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setEndHeading(0);
    m_optionIdVsTaskOptionClass.insert(std::make_pair(uav1, pTaskOptionClass));
    m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());   

    // setting task option for UAV2
    // optionId++;
    // pTaskOptionClass->m_taskOption->setOptionID(optionId);
    // pTaskOptionClass->m_taskOption->getEligibleEntities().push_back(uav2);
    // m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, pTaskOptionClass));
    // m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());  

    std::string compositionString("|(");
    compositionString += "p" + std::to_string(vip) + " p" + std::to_string(uav1) + ")";

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

void VipEscortTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) {
    std::cout << m_VipAirVehicleState->getLocation()->toString() << std::endl;
    std::cout << m_Uav1AirVehicleState->getLocation()->toString() << std::endl;
    // if (m_watchedEntityStateLast)
    // {
    //     // point the camera at the search point
    //     auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
    //     //vehicleActionCommand->setCommandID();
    //     vehicleActionCommand->setVehicleID(entityState->getID());
    //     //vehicleActionCommand->setStatus();
    //     auto gimbalStareAction = new afrl::cmasi::GimbalStareAction;
    //     gimbalStareAction->setStarepoint(m_watchedEntityStateLast->getLocation()->clone());
    //     vehicleActionCommand->getVehicleActionList().push_back(gimbalStareAction);
    //     gimbalStareAction = nullptr; //gave up ownership
    //     // add the loiter
    //     auto loiterAction = new afrl::cmasi::LoiterAction();
    //     loiterAction->setLocation(m_watchedEntityStateLast->getLocation()->clone());
    //     if (m_idVsEntityConfiguration.find(entityState->getID()) != m_idVsEntityConfiguration.end())
    //     {
    //         loiterAction->setAirspeed(m_idVsEntityConfiguration[entityState->getID()]->getNominalSpeed());
    //     }
    //     else
    //     {
    //         CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no EntityConfiguration found for Entity[" << entityState->getID() << "]")
    //     }
    //     loiterAction->setRadius(m_loiterRadius_m);
    //     loiterAction->setAxis(0.0);
    //     loiterAction->setDirection(afrl::cmasi::LoiterDirection::Clockwise);
    //     loiterAction->setDuration(-1.0);
    //     loiterAction->setLength(0.0);
    //     loiterAction->setLoiterType(afrl::cmasi::LoiterType::Circular);
    //     vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
    //     loiterAction = nullptr; //gave up ownership

    //     // send out the response
    //     auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(vehicleActionCommand);
    //     sendSharedLmcpObjectBroadcastMessage(newMessage);
    // }
    // else
    // {
    //     CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no watchedEntityState found for Entity[" << m_watchTask->getWatchedEntityID() << "]")
    // }
}

bool VipEscortTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    auto airVehicleState = std::dynamic_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpObject);
    if (airVehicleState)
    {
        if (airVehicleState->getID() == m_VipEscortTask->getVIP())
        {
            m_VipAirVehicleState = airVehicleState;
        }
        if (airVehicleState->getID() == m_VipEscortTask->getUAV1())
        {
            m_Uav1AirVehicleState = airVehicleState;
        }
        if (airVehicleState->getID() == m_VipEscortTask->getUAV2())
        {
            m_Uav2AirVehicleState = airVehicleState;
        }
    }
    return (false); // always false implies never terminating service from here
};

}; //namespace task
}; //namespace service
}; //namespace uxas

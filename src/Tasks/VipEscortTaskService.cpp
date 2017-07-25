// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   VipEscortTaskService.cpp
 * Author: Mohammed
 *
 * Created on March 22, 2017, 5:55 PM
 *
 * <Service Type="VipEscortTaskService" XXXXX />
 * 
 */
#include "VipEscortTaskService.h"
// include header for this service
#include "afrl/cmasi/AltitudeType.h"
#include "afrl/cmasi/LoiterAction.h"
//include for KeyValuePair LMCP Message
#include "afrl/cmasi/KeyValuePair.h"
#include "afrl/cmasi/Location3D.h"
#include "avtas/lmcp/LmcpXMLReader.h"
#include <Python.h>
#include "uxas/UT/VipEscortTask.h"
#include <iostream>  

#define STRING_XML_ENTITY_STATES "EntityStates"
// namespace definitions
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "CMPS-CMPS-CMPS-CMPS:: XXTsdk:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();

namespace uxas  // uxas::
{
namespace service   // uxas::service::
{
namespace task
{

VipEscortTaskService::ServiceBase::CreationRegistrar<VipEscortTaskService>
VipEscortTaskService::s_registrar(VipEscortTaskService::s_registryServiceTypeNames());

VipEscortTaskService::VipEscortTaskService()
: TaskServiceBase(VipEscortTaskService::s_typeName(), VipEscortTaskService::s_directoryName()) {
 };

VipEscortTaskService::~VipEscortTaskService()
{
    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "::~VipEscortTaskService()");
};

bool
VipEscortTaskService::configureTask(const pugi::xml_node& ndComponent)

{

    setenv("PYTHONPATH", ".", 1);

    Py_Initialize();
    PyRun_SimpleString("import sys");
    PyRun_SimpleString("print((sys.path))");
    Vip_module = PyImport_ImportModule("Vip");
    // Vip_module = PyImport_ImportModule("Simple");
    assert(Vip_module != NULL);

    Vip_class = PyObject_GetAttrString(Vip_module, "Vip");
    // Vip_class = PyObject_GetAttrString(Vip_module, "Simple");
    assert(Vip_class != NULL);

    controller = PyObject_CallObject(Vip_class, NULL);
    assert(controller != NULL);



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

        //creating the list of locations
        afrl::cmasi::Location3D* location1 = new afrl::cmasi::Location3D();
        location1->setLatitude(45.3041);
        location1->setLongitude(-120.9849);
        location1->setAltitude(1000);
        location1->setAltitudeType(m_idVsEntityConfiguration[m_Uav2AirVehicleState->getID()]->getNominalAltitudeType());
        afrl::cmasi::Location3D* location2 = new afrl::cmasi::Location3D();
        location2->setLatitude(45.3041);
        location2->setLongitude(-120.9387);
        location2->setAltitude(1000);
        location2->setAltitudeType(m_idVsEntityConfiguration[m_Uav2AirVehicleState->getID()]->getNominalAltitudeType());
        afrl::cmasi::Location3D* location3 = new afrl::cmasi::Location3D();
        location3->setLatitude(45.3289);
        location3->setLongitude(-120.9635);
        location3->setAltitude(1000);
        location3->setAltitudeType(m_idVsEntityConfiguration[m_Uav2AirVehicleState->getID()]->getNominalAltitudeType());
        afrl::cmasi::Location3D* location4 = new afrl::cmasi::Location3D();
        location4->setLatitude(45.3465);
        location4->setLongitude(-120.9849);
        location4->setAltitude(1000);
        location4->setAltitudeType(m_idVsEntityConfiguration[m_Uav2AirVehicleState->getID()]->getNominalAltitudeType());
        afrl::cmasi::Location3D* location5 = new afrl::cmasi::Location3D();
        location5->setLatitude(45.3465);
        location5->setLongitude(-120.9387);
        location5->setAltitude(1000);
        location5->setAltitudeType(m_idVsEntityConfiguration[m_Uav2AirVehicleState->getID()]->getNominalAltitudeType());

        locations [0] = location1;
        locations [1] = location2;
        locations [2] = location3;
        locations [3] = location4;
        locations [4] = location5;

        //list of flags that correspond to visited locations
        splist[0] = false;
        splist[1] = false;
        splist[2] = false;
        splist[3] = false;
        splist[4] = false;
    }
    return (isSuccessful);

    addSubscriptionAddress(afrl::cmasi::KeyValuePair::Subscription);

    return (isSuccessful);
}

void VipEscortTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

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
    pTaskOptionClass->m_taskOption->setStartLocation(m_VipAirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setStartHeading(0);
    pTaskOptionClass->m_taskOption->setEndLocation(m_Uav1AirVehicleState->getLocation()->clone());
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
    pTaskOptionClass->m_taskOption->setStartLocation(m_Uav1AirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setStartHeading(0);
    pTaskOptionClass->m_taskOption->setEndLocation(m_VipAirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setEndHeading(0);
    m_optionIdVsTaskOptionClass.insert(std::make_pair(uav1, pTaskOptionClass));
    m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());   

    // setting task option for UAV2
    taskOption = new uxas::messages::task::TaskOption;
    taskOption->setTaskID(m_task->getTaskID());
    taskOption->setOptionID(uav2);
    taskOption->getEligibleEntities().clear();
    taskOption->getEligibleEntities().push_back(uav2); // defaults to all entities eligible
    pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
    pTaskOptionClass = std::make_shared<TaskOptionClass>(pTaskOption);
    pTaskOptionClass->m_taskOption->setStartLocation(m_Uav2AirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setStartHeading(0);
    pTaskOptionClass->m_taskOption->setEndLocation(m_VipAirVehicleState->getLocation()->clone());
    pTaskOptionClass->m_taskOption->setEndHeading(0);
    m_optionIdVsTaskOptionClass.insert(std::make_pair(uav2, pTaskOptionClass));
    m_taskPlanOptions->getOptions().push_back(pTaskOptionClass->m_taskOption->clone());   

    std::string compositionString("|(");
    compositionString += "p" + std::to_string(vip) + " p" + std::to_string(uav1) + " p" + std::to_string(uav2) + ")";

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

    return (isSuccessful);
}

bool VipEscortTaskService::initializeTask()
{
    std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

bool VipEscortTaskService::startTask()
{
    std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;



    return (true);
};

bool VipEscortTaskService::terminateTask()
{
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

afrl::cmasi::LoiterAction* VipEscortTaskService::setupLoiter(afrl::cmasi::Location3D* location) {

    auto loiterAction = new afrl::cmasi::LoiterAction();
    loiterAction->setLocation(location);
    loiterAction->setRadius(m_loiterRadius_m);
    loiterAction->setAxis(0.0);
    loiterAction->setDirection(afrl::cmasi::LoiterDirection::Clockwise);
    loiterAction->setDuration(-1.0);
    loiterAction->setLength(0.0);
    loiterAction->setLoiterType(afrl::cmasi::LoiterType::Circular);
    return loiterAction;
}

void VipEscortTaskService::escort(std::shared_ptr<afrl::cmasi::AirVehicleState> escort) {
    if (m_VipAirVehicleState)
    {
        auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
        vehicleActionCommand->setVehicleID(escort->getID());
        auto loiterAction = setupLoiter(locations[vloc]->clone());
        loiterAction->setAirspeed(m_idVsEntityConfiguration[escort->getID()]->getNominalSpeed());//move this to setuploiter function
        loiterAction->getAssociatedTaskList().push_back(m_task->getTaskID());

        vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
        loiterAction = nullptr; //gave up ownership
        // send out the response
        auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(vehicleActionCommand);
        sendSharedLmcpObjectBroadcastMessage(newMessage);
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no watchedEntityState found for Entity[" << m_VipAirVehicleState->getID() << "]")
    }
}

void VipEscortTaskService::gotoLocation(std::shared_ptr<afrl::cmasi::AirVehicleState> uav, int64_t destinationID) {
    if (destinationID != 5)
    {
        if (uav)
        {
            auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
            vehicleActionCommand->setVehicleID(uav->getID());
            vehicleActionCommand->setCommandID(uav->getID());
            // add the loiter
            afrl::cmasi::Location3D* location = locations[destinationID]->clone();
            auto loiterAction = setupLoiter(location);
            loiterAction->setAirspeed(m_idVsEntityConfiguration[uav->getID()]->getNominalSpeed());
            loiterAction->getAssociatedTaskList().push_back(m_task->getTaskID()); //this is needed so no termination happens
            vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
            loiterAction = nullptr; //gave up ownership
            // send out the response
            auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(vehicleActionCommand);
            sendSharedLmcpObjectBroadcastMessage(newMessage);
        }
        else
        {
            CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no watchedEntityState found for Entity[" << uav->getID() << "]")
        }
    }
}

bool VipEscortTaskService::in(std::shared_ptr<afrl::cmasi::AirVehicleState> uav, int location){
    std::cout << "UAV " << uav->getID() << " " << uav->getLocation()->getLatitude() << " " << uav->getLocation()->getLongitude() << std::endl;
    if (uav->getLocation()->getLatitude() < locations[location]->clone()->getLatitude() + 0.0072 && uav->getLocation()->clone()->getLatitude() > locations[location]->clone()->getLatitude() - 0.0072 && 
        uav->getLocation()->getLongitude() < locations[location]->clone()->getLongitude() + 0.0072 && uav->getLocation()->clone()->getLongitude() > locations[location]->clone()->getLongitude() - 0.0072)
        return true;
    else
        return false;
}

int VipEscortTaskService::get_loc(std::shared_ptr<afrl::cmasi::AirVehicleState> uav){
    for (int i = 0; i < 5; ++i)
    {
        if (in(uav,i))
        {
            if (uav->getID()== m_Uav2AirVehicleState->getID())
            {
                uav2_previous_loc = i;
                splist[i] = true;  
            }
            else if (uav->getID()== m_Uav1AirVehicleState->getID())
            {
                uav1_previous_loc = i;
                splist[i] = true;  
            }  
            else if (uav->getID()== m_VipAirVehicleState->getID())
            {
                uavVIP_previous_loc = i;
                // splist[i] = true;  
            }      
            return i;
        }
    }

    if (uav->getID() == m_Uav2AirVehicleState->getID())
    {
        return uav2_previous_loc;
    }
    else if (uav->getID() == m_Uav1AirVehicleState->getID())
    {
        return uav1_previous_loc;
    }   
    else if (uav->getID() == m_VipAirVehicleState->getID())
    {
        return uavVIP_previous_loc;
    }    
}

void VipEscortTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) {

    // // escort(m_Uav1AirVehicleState);
    // // gotoLocation(m_VipAirVehicleState,3);
    // std::cout << "UAV " << m_Uav1AirVehicleState->getID() << " " << m_Uav1AirVehicleState->getLocation()->getLatitude() << " " << m_Uav1AirVehicleState->getLocation()->getLongitude() << std::endl;

    if (initial)
    {
        std::cout << "START?" << std::endl;
        auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
        vehicleActionCommand->setVehicleID(m_Uav1AirVehicleState->getID());
        vehicleActionCommand->setCommandID(m_Uav1AirVehicleState->getID());
        // add the loiter
        afrl::cmasi::Location3D* location = locations[4]->clone();
        auto loiterAction = setupLoiter(location);
        loiterAction->setAirspeed(m_idVsEntityConfiguration[m_Uav1AirVehicleState->getID()]->getNominalSpeed());
        loiterAction->getAssociatedTaskList().push_back(m_task->getTaskID()); //this is needed so no termination happens
        vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
        loiterAction = nullptr; //gave up ownership
        // send out the response
        auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(vehicleActionCommand);
        sendSharedLmcpObjectBroadcastMessage(newMessage);
        initial = false;
    }
    
    counter++;
    // if (vTrack1)
    // {
    //     escort(m_Uav1AirVehicleState);
    // }
    // if (vTrack2)
    // {
    //     escort(m_Uav2AirVehicleState);
    // }

    if (counter > 950)
    {
        std::cout << "START" << std::endl;
        int l_vip = get_loc(m_VipAirVehicleState);
        int l_1 = get_loc(m_Uav1AirVehicleState);
        int l_2 = get_loc(m_Uav2AirVehicleState);
        std::cout << "VIP: " << l_vip << std::endl;
        std::cout << "UAV1: " << l_1 << std::endl;
        std::cout << "UAV2: " << l_2 << std::endl;

        PyObject* result = PyObject_CallMethod(controller, "move","(iiiiiiii)", splist[0],splist[1],
            splist[2],splist[3],splist[4],l_vip,
            l_1,l_2);

        assert(result != NULL);
        vloc = std::stoi(PyString_AsString(PyObject_Repr(PyDict_GetItem(result, PyString_FromString("vloc")))));
        bool vTrack1 = PyObject_IsTrue(PyDict_GetItem(result, PyString_FromString("vTrack1")));
        std::cout << "UAV1 Track: " << vTrack1 << std::endl;
        if (vTrack1)
        {
            escort(m_Uav1AirVehicleState);
        }
        bool vTrack2 = PyObject_IsTrue(PyDict_GetItem(result, PyString_FromString("vTrack2")));
        std::cout << "UAV2 Track: " << vTrack2 << std::endl;
        if (vTrack2)
        {
            escort(m_Uav2AirVehicleState);
        }
        
        std::cout << "VIP next: " << vloc << std::endl;
        gotoLocation(m_VipAirVehicleState,vloc);
        int uloc1 = std::stoi(PyString_AsString(PyObject_Repr(PyDict_GetItem(result, PyString_FromString("uloc1")))));
        std::cout << "UAV1 next: " << uloc1 << std::endl;
        gotoLocation(m_Uav1AirVehicleState,uloc1);
        int uloc2 = std::stoi(PyString_AsString(PyObject_Repr(PyDict_GetItem(result, PyString_FromString("uloc2")))));
        std::cout << "UAV2 next: " << uloc2 << std::endl;
        gotoLocation(m_Uav2AirVehicleState,uloc2);
        counter = 0;
    }
}


// void VipEscortTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) {

//     // // escort(m_Uav1AirVehicleState);
//     // // gotoLocation(m_VipAirVehicleState,3);
    
//     if (initial)
//     {
//         std::cout << "START?" << std::endl;
//         auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
//         vehicleActionCommand->setVehicleID(m_Uav1AirVehicleState->getID());
//         vehicleActionCommand->setCommandID(m_Uav1AirVehicleState->getID());
//         // add the loiter
//         afrl::cmasi::Location3D* location = locations[4]->clone();
//         auto loiterAction = setupLoiter(location);
//         loiterAction->setAirspeed(m_idVsEntityConfiguration[m_Uav1AirVehicleState->getID()]->getNominalSpeed());
//         loiterAction->getAssociatedTaskList().push_back(m_task->getTaskID()); //this is needed so no termination happens
//         vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
//         loiterAction = nullptr; //gave up ownership
//         // send out the response
//         auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(vehicleActionCommand);
//         sendSharedLmcpObjectBroadcastMessage(newMessage);
//         initial = false;
//     }
    
//     counter++;
//     std::cout << counter << std::endl;
    
//     if (counter > 500)
//     {
//         std::cout << "START" << std::endl;

//         std::cout << "VIP: " << get_loc(m_VipAirVehicleState) << std::endl;
//         std::cout << "UAV1: " << get_loc(m_Uav1AirVehicleState) << std::endl;
//         std::cout << "UAV2: " << get_loc(m_Uav2AirVehicleState) << std::endl;

//         // PyObject* result = PyObject_CallMethod(controller, "move","(iiiiiiii)", splist[0],splist[1],
//         //     splist[2],splist[3],splist[4],get_loc(m_VipAirVehicleState),
//         //     get_loc(m_Uav1AirVehicleState),get_loc(m_Uav2AirVehicleState));

//         PyObject* result = PyObject_CallMethod(controller, "move","i", get_loc(m_VipAirVehicleState));

//         assert(result != NULL);
//         // bool vTrack1 = PyObject_IsTrue(PyDict_GetItem(result, PyString_FromString("vTrack1")));
//         // std::cout << "UAV1 Track: " << vTrack1 << std::endl;
//         // if (vTrack1)
//         // {
//         //     escort(m_Uav1AirVehicleState);
//         // }
//         // bool vTrack2 = PyObject_IsTrue(PyDict_GetItem(result, PyString_FromString("vTrack2")));
//         // std::cout << "UAV2 Track: " << vTrack1 << std::endl;
//         // if (vTrack2)
//         // {
//         //     escort(m_Uav2AirVehicleState);
//         // }
//         std::cout << PyString_AsString(PyObject_Repr(PyDict_GetItem(result, PyString_FromString("vlo")))) << std::endl;
//         int vloc = std::stoi(PyString_AsString(PyObject_Repr(PyDict_GetItem(result, PyString_FromString("vloc")))));
//         std::cout << "VIP next: " << vloc << std::endl;
//         gotoLocation(m_VipAirVehicleState,vloc);
//         // int uloc1 = std::stoi(PyString_AsString(PyObject_Repr(PyDict_GetItem(result, PyString_FromString("uloc1")))));
//         // std::cout << "UAV1 next: " << uloc1 << std::endl;
//         // gotoLocation(m_Uav1AirVehicleState,uloc1);
//         // int uloc2 = std::stoi(PyString_AsString(PyObject_Repr(PyDict_GetItem(result, PyString_FromString("uloc2")))));
//         // std::cout << "UAV2 next: " << uloc2 << std::endl;
//         // gotoLocation(m_Uav2AirVehicleState,uloc2);
//         counter = 0;
//     }
// }


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
        else if (airVehicleState->getID() == m_VipEscortTask->getUAV1())
        {
            m_Uav1AirVehicleState = airVehicleState;
        }
        else if (airVehicleState->getID() == m_VipEscortTask->getUAV2())
        {
            m_Uav2AirVehicleState = airVehicleState;
        }
    }
    return (false); // always false implies never terminating service from here
};

}; //namespace task
}; //namespace service
}; //namespace uxas

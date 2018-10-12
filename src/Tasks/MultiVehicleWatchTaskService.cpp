// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_MultiVehicleWatchTask.cpp
 * Author: Derek & steve
 *
 * Created on March 7, 2016, 6:17 PM
 */


#include "MultiVehicleWatchTaskService.h"

#include "Position.h"
#include "UnitConversions.h"

#include "avtas/lmcp/LmcpXMLReader.h"
#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/LoiterAction.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/vehicles/GroundVehicleConfiguration.h"
#include "afrl/vehicles/SurfaceVehicleConfiguration.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RouteResponse.h"
#include "uxas/messages/route/RouteConstraints.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"
#include "DpssDataTypes.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc

#define STRING_XML_ENTITY_STATES "EntityStates" //TODO:: define this in some global place

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "MVWT-MVWT-MVWT-MVWT:: MultiVehicleWatchTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "MVWT-MVWT-MVWT-MVWT:: MultiVehicleWatchTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
MultiVehicleWatchTaskService::ServiceBase::CreationRegistrar<MultiVehicleWatchTaskService>
MultiVehicleWatchTaskService::s_registrar(MultiVehicleWatchTaskService::s_registryServiceTypeNames());

MultiVehicleWatchTaskService::MultiVehicleWatchTaskService()
: TaskServiceBase(MultiVehicleWatchTaskService::s_typeName(), MultiVehicleWatchTaskService::s_directoryName())
{
};

MultiVehicleWatchTaskService::~MultiVehicleWatchTaskService()
{
};

bool
MultiVehicleWatchTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isMultiVehicleWatchTask(m_task.get()))
        {
            m_MultiVehicleWatchTask = std::static_pointer_cast<afrl::impact::MultiVehicleWatchTask>(m_task);
            if (!m_MultiVehicleWatchTask)
            {
                sstrErrors << "ERROR:: **MultiVehicleWatchTaskService::bConfigure failed to cast a MultiVehicleWatchTask from the task pointer." << std::endl;
                CERR_FILE_LINE_MSG(sstrErrors.str())
                isSuccessful = false;
            }
        }
        else
        {
            sstrErrors << "ERROR:: **MultiVehicleWatchTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a MultiVehicleWatchTask." << std::endl;
            CERR_FILE_LINE_MSG(sstrErrors.str())
            isSuccessful = false;
        }
    } //isSuccessful
    if (isSuccessful)
    {
        if (m_entityStates.find(m_MultiVehicleWatchTask->getWatchedEntityID()) != m_entityStates.end())
        {
            m_watchedEntityStateLast = m_entityStates[m_MultiVehicleWatchTask->getWatchedEntityID()];
        }

    } //if(isSuccessful)
    return (isSuccessful);
}

bool
MultiVehicleWatchTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpObject);
    if (entityState)
    {
        if (entityState->getID() == m_MultiVehicleWatchTask->getWatchedEntityID())
        {
            m_watchedEntityStateLast = entityState;
        }
        m_idVsEntityState[entityState->getID()] = entityState;
    }
    return (false); // always false implies never terminating service from here
};

void MultiVehicleWatchTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

    // this task enforces option ID equal to vehicle ID

    int64_t taskId(m_MultiVehicleWatchTask->getTaskID());

    //        m_speedAltitudeVsEligibleEntitesRequested
    //        m_blockadeTask->getNumberVehicles();
    for (auto& eligibleEntitesRequested : m_speedAltitudeVsEligibleEntityIdsRequested)
    {
        for (auto& entityId : eligibleEntitesRequested.second)
        {
            if (!isCalculateOption(taskId, entityId))
            {
                isSuccessful = false;
            }
        }
    }

    size_t N = m_MultiVehicleWatchTask->getNumberVehicles();
    if (m_speedAltitudeVsEligibleEntityIdsRequested.size() < N)
    {
        N = m_speedAltitudeVsEligibleEntityIdsRequested.size();
    }

    // TODO: efficiently present all combinations/permutations
    // for now just use all eligible vehicles from automation request
    std::string compositionString(".(");
    for (auto& eligibleEntitesRequested : m_speedAltitudeVsEligibleEntityIdsRequested)
    {
        for (auto& entityId : eligibleEntitesRequested.second)
        {
            compositionString += "p";
            compositionString += std::to_string(entityId);
            compositionString += " ";
        }
    }
    compositionString += ")";

    m_taskPlanOptions->setComposition(compositionString);

    // send out the options
    if (isSuccessful)
    {
        auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
        sendSharedLmcpObjectBroadcastMessage(newResponse);
    }
};

bool MultiVehicleWatchTaskService::isCalculateOption(const int64_t& taskId, int64_t & optionId)
{
    bool isSuccessful{true};

    if (m_watchedEntityStateLast)
    {
        auto taskOption = new uxas::messages::task::TaskOption;
        taskOption->getEligibleEntities().push_back(optionId); // note: this task enforces optionId == entityId
        taskOption->setTaskID(taskId);
        taskOption->setOptionID(optionId);
        taskOption->setStartLocation(m_watchedEntityStateLast->getLocation()->clone());
        taskOption->setStartHeading(m_watchedEntityStateLast->getHeading());
        taskOption->setEndLocation(m_watchedEntityStateLast->getLocation()->clone());
        taskOption->setEndHeading(m_watchedEntityStateLast->getHeading());
        auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
        m_taskPlanOptions->getOptions().push_back(taskOption);
        taskOption = nullptr; //just gave up ownership
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::Task_MultiVehicleWatchTask:: no blockedEntityState found for Entity[" << m_MultiVehicleWatchTask->getWatchedEntityID() << "]")
        isSuccessful = false;
    }

    return (isSuccessful);
}

void MultiVehicleWatchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    if (m_watchedEntityStateLast)
    {
        // fill in neighbor set
        std::vector< int64_t > neighborIds;
        for (auto activeEntity : m_activeEntities)
        {
            neighborIds.push_back(activeEntity);
        }

        // at this point, all neighbors have valid positions and are considered cooperating on task
        auto actionCommand = CalculateGimbalActions(entityState, m_watchedEntityStateLast->getLocation()->getLatitude(), m_watchedEntityStateLast->getLocation()->getLongitude());

        //auto pResponse = std::static_pointer_cast<avtas::lmcp::Object>(actionCommand);
        auto pResponse = std::shared_ptr<avtas::lmcp::Object>(actionCommand);
        sendSharedLmcpObjectBroadcastMessage(pResponse);
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::Task_MultiVehicleWatchTask:: no watchedEntityState found for Entity[" << m_MultiVehicleWatchTask->getWatchedEntityID() << "]")
    }
}

std::shared_ptr<afrl::cmasi::VehicleActionCommand> MultiVehicleWatchTaskService::CalculateGimbalActions(const std::shared_ptr<afrl::cmasi::EntityState>& entityState, double lat, double lon)
{
    std::shared_ptr<afrl::cmasi::VehicleActionCommand> caction(new afrl::cmasi::VehicleActionCommand);
    caction->setVehicleID(entityState->getID());
    double surveyRadius = 300.0; // default 300 meters, circular
    double surveySpeed = entityState->getGroundspeed();
    auto surveyType = afrl::cmasi::LoiterType::Circular;
    std::vector<int64_t> gimbalId;

    if (m_entityConfigurations.find(entityState->getID()) != m_entityConfigurations.end())
    {
        surveySpeed = m_entityConfigurations[entityState->getID()]->getNominalSpeed();
        // find all gimbals to steer
        for (size_t a = 0; a < m_entityConfigurations[entityState->getID()]->getPayloadConfigurationList().size(); a++)
        {
            auto payload = m_entityConfigurations[entityState->getID()]->getPayloadConfigurationList().at(a);
            if (afrl::cmasi::isGimbalConfiguration(payload))
            {
                gimbalId.push_back(payload->getPayloadID());
            }
        }

        // calculate proper radius
        if (afrl::vehicles::isGroundVehicleConfiguration(m_entityConfigurations[entityState->getID()].get()) ||
                afrl::vehicles::isSurfaceVehicleConfiguration(m_entityConfigurations[entityState->getID()].get()))
        {
            surveyRadius = 0.0;
            surveyType = afrl::cmasi::LoiterType::Hover;
        }
        else if (afrl::cmasi::isAirVehicleConfiguration(m_entityConfigurations[entityState->getID()].get()))
        {
            double speed = m_entityConfigurations[entityState->getID()]->getNominalSpeed();
            double bank = 25.0 * n_Const::c_Convert::dDegreesToRadians();
            // Note: R = V/omega for coordinated turn omega = g*tan(phi)/V
            // Therefore: R = V^2/(g*tan(phi))
            surveyRadius = speed * speed / (9.80665 * tan(bank));
            // round up to the nearest 100m
            surveyRadius = std::ceil(surveyRadius / 100.0)*100.0;

            // TODO: sometimes the loiter radius seems to change size, so hard-code
            surveyRadius = 300.0;
        }
    }

    afrl::cmasi::LoiterAction* surveyAction = new afrl::cmasi::LoiterAction;
    surveyAction->setLocation(new afrl::cmasi::Location3D());
    surveyAction->getLocation()->setLatitude(lat);
    surveyAction->getLocation()->setLongitude(lon);
    surveyAction->getLocation()->setAltitude(entityState->getLocation()->getAltitude());
    surveyAction->getLocation()->setAltitudeType(entityState->getLocation()->getAltitudeType());
    surveyAction->setAirspeed(surveySpeed);
    surveyAction->setRadius(surveyRadius);
    surveyAction->setDirection(afrl::cmasi::LoiterDirection::CounterClockwise);
    surveyAction->setDuration(-1);
    surveyAction->setLoiterType(surveyType);
    surveyAction->getAssociatedTaskList().push_back(m_task->getTaskID());
    caction->getVehicleActionList().push_back(surveyAction);

    // steer all gimbals
    for (size_t g = 0; g < gimbalId.size(); g++)
    {
        afrl::cmasi::GimbalStareAction* gimbalAction = new afrl::cmasi::GimbalStareAction;
        gimbalAction->setDuration(-1);
        gimbalAction->setPayloadID(gimbalId.at(g));
        gimbalAction->setStarepoint(m_watchedEntityStateLast->getLocation()->clone());
        gimbalAction->getAssociatedTaskList().push_back(m_task->getTaskID());
        caction->getVehicleActionList().push_back(gimbalAction->clone());
    }

    return caction;
}

}; //namespace task
}; //namespace service
}; //namespace uxas

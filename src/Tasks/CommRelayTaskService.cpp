// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_CommRelayTask.cpp
 * Author: Derek & steve
 *
 * Created on March 7, 2016, 6:17 PM
 */


#include "CommRelayTaskService.h"

#include "Position.h"
#include "UnitConversions.h"

#include "avtas/lmcp/LmcpXMLReader.h"
#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/LoiterAction.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/impact/GroundVehicleConfiguration.h"
#include "afrl/impact/SurfaceVehicleConfiguration.h"
#include "afrl/impact/RadioTowerConfiguration.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/impact/GroundVehicleState.h"
#include "afrl/impact/SurfaceVehicleState.h"
#include "afrl/impact/RadioTowerState.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RouteResponse.h"
#include "uxas/messages/route/RouteConstraints.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"
#include "DpssDataTypes.h"
#include "TimeUtilities.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc


#define STRING_XML_ENTITY_STATES "EntityStates" //TODO:: define this in some global place

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "MVWT-MVWT-MVWT-MVWT:: CommRelayTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "MVWT-MVWT-MVWT-MVWT:: CommRelayTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
CommRelayTaskService::ServiceBase::CreationRegistrar<CommRelayTaskService>
CommRelayTaskService::s_registrar(CommRelayTaskService::s_registryServiceTypeNames());

CommRelayTaskService::CommRelayTaskService()
: TaskServiceBase(CommRelayTaskService::s_typeName(), CommRelayTaskService::s_directoryName())
{
};

CommRelayTaskService::~CommRelayTaskService()
{
};

bool
CommRelayTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    std::stringstream sstrErrors;

    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isCommRelayTask(m_task.get()))
        {
            m_CommRelayTask = std::static_pointer_cast<afrl::impact::CommRelayTask>(m_task);
            if (!m_CommRelayTask)
            {
                sstrErrors << "ERROR:: **CommRelayTaskService::bConfigure failed to cast a CommRelayTask from the task pointer." << std::endl;
                CERR_FILE_LINE_MSG(sstrErrors.str())
                isSuccessful = false;
            }
        }
        else
        {
            sstrErrors << "ERROR:: **CommRelayTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a CommRelayTask." << std::endl;
            CERR_FILE_LINE_MSG(sstrErrors.str())
            isSuccessful = false;
        }
    } //isSuccessful
    if (isSuccessful)
    {
        pugi::xml_node entityStates = ndComponent.child(STRING_XML_ENTITY_STATES);
        if (entityStates)
        {
            for (auto ndEntityState = entityStates.first_child(); ndEntityState; ndEntityState = ndEntityState.next_sibling())
            {

                std::shared_ptr<afrl::cmasi::EntityState> entityState;
                std::stringstream stringStream;
                ndEntityState.print(stringStream);
                avtas::lmcp::Object* object = avtas::lmcp::xml::readXML(stringStream.str());
                if (object != nullptr)
                {
                    entityState.reset(static_cast<afrl::cmasi::EntityState*> (object));
                    object = nullptr;

                    if (entityState->getID() == m_CommRelayTask->getSupportedEntityID())
                    {
                        m_supportedEntityStateLast = entityState;
                    }
                    m_idVsEntityState[entityState->getID()] = entityState;
                }
            }
        }
    } //if(isSuccessful)
    return (isSuccessful);
}

bool
CommRelayTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpObject);
    if (entityState)
    {
        if (entityState->getID() == m_CommRelayTask->getSupportedEntityID())
        {
            m_supportedEntityStateLast = entityState;
        }
        m_idVsEntityState[entityState->getID()] = entityState;
    }
    return (false); // always false implies never terminating service from here
};

void CommRelayTaskService::buildTaskPlanOptions()
{
    bool isSuccessful{true};

    int64_t optionId(1);
    int64_t taskId(m_CommRelayTask->getTaskID());

    if (isCalculateOption(taskId, optionId))
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

    m_taskPlanOptions->setComposition(compositionString);

    // send out the options
    if (isSuccessful)
    {
        auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
        sendSharedLmcpObjectBroadcastMessage(newResponse);
    }
};

bool CommRelayTaskService::isCalculateOption(const int64_t& taskId, int64_t & optionId)
{
    bool isSuccessful{true};

    if (m_supportedEntityStateLast)
    {
        auto taskOption = new uxas::messages::task::TaskOption;
        taskOption->setTaskID(taskId);
        taskOption->setOptionID(optionId);
        taskOption->getEligibleEntities() = m_CommRelayTask->getEligibleEntities();
        taskOption->setStartLocation(m_supportedEntityStateLast->getLocation()->clone());
        taskOption->setStartHeading(m_supportedEntityStateLast->getHeading());
        taskOption->setEndLocation(m_supportedEntityStateLast->getLocation()->clone());
        taskOption->setEndHeading(m_supportedEntityStateLast->getHeading());
        auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
        m_taskPlanOptions->getOptions().push_back(taskOption);
        taskOption = nullptr; //just gave up ownership

    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::Task_CommRelayTask:: no watchedEntityState found for Entity[" << m_CommRelayTask->getSupportedEntityID() << "]")
        isSuccessful = false;
    }

    return (isSuccessful);
}

void CommRelayTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    if (m_supportedEntityStateLast)
    {
        // initialize throttle per vehicle
        if (m_throttle.find(entityState->getID()) == m_throttle.end())
        {
            m_throttle[entityState->getID()] = uxas::common::utilities::c_TimeUtilities::getTimeNow_ms();
        }

        // only send out every 2 seconds (even on fast simulation mode)
        if (!afrl::impact::isGroundVehicleState(entityState.get()) || m_throttle[entityState->getID()] + 2000 <= uxas::common::utilities::c_TimeUtilities::getTimeNow_ms())
        {
            m_throttle[entityState->getID()] = uxas::common::utilities::c_TimeUtilities::getTimeNow_ms();
        }
        else
        {
            return;
        }

        // look up speed to use for commanding vehicle
        double speed = entityState->getGroundspeed();
        if (m_entityConfigurations.find(entityState->getID()) != m_entityConfigurations.end())
        {
            speed = m_entityConfigurations[entityState->getID()]->getNominalSpeed();
        }

        // extract location of tower
        int64_t towerId = m_CommRelayTask->getTowerID();
        std::shared_ptr<afrl::cmasi::Location3D> towerLocation{nullptr};

        if (m_idVsEntityState.find(towerId) != m_idVsEntityState.end())
        {
            towerLocation.reset(m_idVsEntityState[towerId]->getLocation()->clone());
        }

        if (!towerLocation)
        {
            if (m_entityConfigurations.find(towerId) != m_entityConfigurations.end())
            {
                if (afrl::impact::isRadioTowerConfiguration(m_entityConfigurations[towerId].get()))
                {
                    auto config = std::static_pointer_cast<afrl::impact::RadioTowerConfiguration>(m_entityConfigurations[towerId]);
                    towerLocation.reset(config->getPosition()->clone());
                }
            }
        }

        if (!towerLocation) // don't care if not enabled, still attempt relay
            return;

        // determine destination location
        uxas::common::utilities::CUnitConversions flatEarth;
        double north, east;
        flatEarth.ConvertLatLong_degToNorthEast_m(towerLocation->getLatitude(), towerLocation->getLongitude(), north, east);
        Dpss_Data_n::xyPoint tower(east, north);
        flatEarth.ConvertLatLong_degToNorthEast_m(m_supportedEntityStateLast->getLocation()->getLatitude(), m_supportedEntityStateLast->getLocation()->getLongitude(), north, east);
        Dpss_Data_n::xyPoint target(east, north);

        // go halfway between 'targetLocation' and 'tower' TODO: make this more efficient?
        target.x = (tower.x + target.x) / 2;
        target.y = (tower.y + target.y) / 2;

        // back to lat/lon
        double lat, lon;
        flatEarth.ConvertNorthEast_mToLatLong_deg(target.y, target.x, lat, lon);

        // at this point, all neighbors have valid positions and are considered cooperating on task
        auto actionCommand = CalculateGimbalActions(entityState, lat, lon);

        // build mini-mission of two waypoint with hover action at end
        auto missionCommand = new afrl::cmasi::MissionCommand;
        missionCommand->setCommandID(getUniqueEntitySendMessageId());
        missionCommand->setFirstWaypoint(1);
        missionCommand->setVehicleID(entityState->getID());
        auto wp = new afrl::cmasi::Waypoint;
        wp->setAltitude(entityState->getLocation()->getAltitude());
        wp->setAltitudeType(entityState->getLocation()->getAltitudeType());
        wp->setLatitude(lat);
        wp->setLongitude(lon);
        wp->setNextWaypoint(1);
        wp->setNumber(1);
        wp->setSpeed(speed);
        wp->setTurnType(afrl::cmasi::TurnType::TurnShort);
        wp->getAssociatedTasks().push_back(m_task->getTaskID());
        missionCommand->getWaypointList().push_back(wp);

        for (size_t a = 0; a < actionCommand->getVehicleActionList().size(); a++)
        {
            auto act = actionCommand->getVehicleActionList().at(a);
            wp->getVehicleActionList().push_back(act->clone());
        }
        missionCommand->getWaypointList().push_back(wp);

        // check if surface or ground vehicle
        if ((afrl::impact::isSurfaceVehicleState(entityState.get()) || afrl::impact::isGroundVehicleState(entityState.get())) && !missionCommand->getWaypointList().empty())
        {
            afrl::cmasi::Waypoint* hwp = wp->clone();
            hwp->setNumber(2);
            hwp->setNextWaypoint(2);
            missionCommand->getWaypointList().front()->setNextWaypoint(2);
            for (auto a : missionCommand->getWaypointList().front()->getVehicleActionList())
            {
                delete a;
            }
            missionCommand->getWaypointList().front()->getVehicleActionList().clear();
            missionCommand->getWaypointList().push_back(hwp);
        }
        else
        {
            for (auto wypt : missionCommand->getWaypointList())
            {
                delete wypt;
            }
            missionCommand->getWaypointList().clear();
        }

        // send response
        std::shared_ptr<avtas::lmcp::Object> pResponse;

        // single waypoint mission command instead of action (if possible)
        if (!missionCommand->getWaypointList().empty())
        {
            pResponse = std::shared_ptr<avtas::lmcp::Object>(missionCommand);
        }
        else
        {
            delete missionCommand;
            pResponse = std::static_pointer_cast<avtas::lmcp::Object>(actionCommand);
        }
        sendSharedLmcpObjectBroadcastMessage(pResponse);
    }
    else
    {
        CERR_FILE_LINE_MSG("ERROR::Task_CommRelayTask:: no watchedEntityState found for Entity[" << m_CommRelayTask->getSupportedEntityID() << "]")
    }
}

std::shared_ptr<afrl::cmasi::VehicleActionCommand> CommRelayTaskService::CalculateGimbalActions(const std::shared_ptr<afrl::cmasi::EntityState>& entityState, double lat, double lon)
{
    std::shared_ptr<afrl::cmasi::VehicleActionCommand> caction(new afrl::cmasi::VehicleActionCommand);

    double surveyRadius = m_loiterRadius_m;
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
        if (afrl::impact::isGroundVehicleConfiguration(m_entityConfigurations[entityState->getID()].get()) ||
                afrl::impact::isSurfaceVehicleConfiguration(m_entityConfigurations[entityState->getID()].get()))
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
            surveyRadius = m_loiterRadius_m;
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
        gimbalAction->setStarepoint(m_supportedEntityStateLast->getLocation()->clone());
        gimbalAction->getAssociatedTaskList().push_back(m_task->getTaskID());
        caction->getVehicleActionList().push_back(gimbalAction->clone());
    }

    return caction;
}

}; //namespace task
}; //namespace service
}; //namespace uxas

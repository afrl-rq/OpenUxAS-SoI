// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_WatchTask.cpp
 * Author: steve
 * 
 * Created on February 24, 2016, 6:17 PM
 */


#include "OverwatchTaskService.h"

#include "Position.h"
#include "FlatEarth.h"

#include "avtas/lmcp/LmcpXMLReader.h"
#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/GimbalStareAction.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "afrl/cmasi/LoiterAction.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/RouteRequest.h"
#include "uxas/messages/route/RouteResponse.h"
#include "uxas/messages/route/RouteConstraints.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <fstream>
#include <boost/filesystem.hpp>

#define STRING_XML_ENTITY_STATES "EntityStates" //TODO:: define this in some global place

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "CMPS-CMPS-CMPS-CMPS:: WatchTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "CMPS-CMPS-CMPS-CMPS:: WatchTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{
namespace task
{
OverwatchTaskService::ServiceBase::CreationRegistrar<OverwatchTaskService>
OverwatchTaskService::s_registrar(OverwatchTaskService::s_registryServiceTypeNames());

OverwatchTaskService::OverwatchTaskService()
: TaskServiceBase(OverwatchTaskService::s_typeName(), OverwatchTaskService::s_directoryName())
{
    m_isMakeTransitionWaypointsActive = true;
}

OverwatchTaskService::~OverwatchTaskService()
{
}

bool
OverwatchTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    std::stringstream sstrErrors;

    if (afrl::impact::isWatchTask(m_task.get()))
    {
        m_watchTask = std::static_pointer_cast<afrl::impact::WatchTask>(m_task);
        if (!m_watchTask)
        {
            sstrErrors << "ERROR:: **OverwatchTaskService::bConfigure failed to cast a WatchTask from the task pointer." << std::endl;
            CERR_FILE_LINE_MSG(sstrErrors.str())
            return false;
        }
    }
    else
    {
        sstrErrors << "ERROR:: **OverwatchTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a WatchTask." << std::endl;
        CERR_FILE_LINE_MSG(sstrErrors.str())
        return false;
    }

    // try to find entity states listed in the configuration
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

                if (entityState->getID() == m_watchTask->getWatchedEntityID())
                {
                    m_watchedEntityStateLast = entityState;
                    break;
                }
            }
        }
    }

    // look for watched entity state in base storage
    for(auto st : m_entityStates)
    {
        if(st.second->getID() == m_watchTask->getWatchedEntityID())
        {
            m_watchedEntityStateLast = st.second;
            break;
        }
    }

    // create initial logs
    std::ofstream estfile;
    estfile.open(m_workDirectoryPath + "/" + "estimated.csv", std::ios_base::app);
    estfile << "# time (ms since 1 Jan 1970), lat (deg), lon (deg), speed (m/s), heading (deg)" << std::endl;
    estfile.close();

    std::ofstream mesfile;
    mesfile.open(m_workDirectoryPath + "/" + "measured.csv", std::ios_base::app);
    mesfile << "# time (ms since 1 Jan 1970), lat (deg), lon (deg), speed (m/s), heading (deg)" << std::endl;
    mesfile.close();

    return (true);
}

bool
OverwatchTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
{
    // track watched entity
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpObject);
    if (entityState)
    {
        if (entityState->getID() == m_watchTask->getWatchedEntityID())
        {
            if( fabs(entityState->getLocation()->getLatitude()) < 0.01 && fabs(entityState->getLocation()->getLongitude()) < 0.01 )
                return false;

            // add to measured entity log
            // time (ms since 1 Jan 1970), lat (deg), lon (deg), speed (m/s), heading (deg)
            bool addlogheader = false;
            if( !boost::filesystem::exists( m_workDirectoryPath + "/" + "measured.csv" ) )
                addlogheader = true;

            std::ofstream logfile;
            logfile.open(m_workDirectoryPath + "/" + "measured.csv", std::ios_base::app);
            if(addlogheader)
                logfile << "# time (ms since 1 Jan 1970), lat (deg), lon (deg), speed (m/s), heading (deg)" << std::endl;
            logfile << entityState->getTime() << ",";
            logfile << entityState->getLocation()->getLatitude() << ",";
            logfile << entityState->getLocation()->getLongitude() << ",";
            logfile << "0.0,0.0" << std::endl;
            logfile.close();

            m_watchedEntityWindow.push_back(entityState);
            while(m_watchedEntityWindow.size() > m_windowSize)
                m_watchedEntityWindow.pop_front();
            m_watchedEntityStateLast = entityState;
        }
    }
    return (false); // always false implies never terminating service from here
}

void OverwatchTaskService::buildTaskPlanOptions()
{
    int64_t optionId(TaskOptionClass::m_firstOptionId);
    int64_t taskId(m_watchTask->getTaskID());

    // build a single option for all eligible vehicles
    if (isCalculateOption(taskId, optionId, m_watchTask->getEligibleEntities()))
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

    auto newResponse = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
    sendSharedLmcpObjectBroadcastMessage(newResponse);
}

bool OverwatchTaskService::isCalculateOption(const int64_t& taskId, int64_t& optionId, const std::vector<int64_t>& eligibleEntities)
{
    if (m_watchedEntityStateLast)
    {
        auto taskOption = new uxas::messages::task::TaskOption;
        taskOption->setTaskID(taskId);
        taskOption->setOptionID(optionId);
        taskOption->getEligibleEntities() = eligibleEntities;
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
        CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no watchedEntityState found for Entity[" << m_watchTask->getWatchedEntityID() << "]")
        return false;
    }

    return true;
}

void OverwatchTaskService::activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState)
{
    // if no valid watch state, do nothing
    if(!m_watchedEntityStateLast)
    {
        CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no watchedEntityState found for Entity[" << m_watchTask->getWatchedEntityID() << "]")
        return;
    }

    // if no watch track is stale, do nothing
    int64_t dt = entityState->getTime() - m_watchedEntityStateLast->getTime();
    if(dt > 15000)
    {
        CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: stale watch state [" << m_watchTask->getWatchedEntityID() << "]: " << dt)
        return;
    }

    // project state based on constant velocity assumption
    auto projstate = std::shared_ptr<afrl::cmasi::EntityState>(m_watchedEntityStateLast->clone());

    // if estimating, start with zero expected motion
    if(m_estimateTargetMotion)
    {
        projstate->setGroundspeed(0.0);
        projstate->setHeading(0.0);
        projstate->setCourse(0.0);
    }

    // if we have enough samples, average heading/speed over window
    if(m_estimateTargetMotion && m_watchedEntityWindow.size() > 1)
    {
        auto prev = m_watchedEntityWindow.front();
        double speed_est = 0.0;
        double cosheading = 0.0;
        double sinheading = 0.0;
        size_t Nsamples = 0;
        for(auto i=1; i<m_watchedEntityWindow.size(); i++)
        {
            auto cur = m_watchedEntityWindow.at(i);

            // throw out crazy samples that are too close or too far away
            double del_t = (cur->getTime() - prev->getTime())/1000.0;
            if(del_t < 0.01) continue;
            if(del_t > 4.0) { prev = cur; continue; }

            // project to plane for heading and speed calculation
            uxas::common::utilities::FlatEarth flatEarth;
            double pnorth, peast, cnorth, ceast;
            flatEarth.ConvertLatLong_degToNorthEast_m(prev->getLocation()->getLatitude(), prev->getLocation()->getLongitude(), pnorth, peast);
            flatEarth.ConvertLatLong_degToNorthEast_m(cur->getLocation()->getLatitude(), cur->getLocation()->getLongitude(), cnorth, ceast);

            Nsamples++;
            prev = cur;

            double dnorth = cnorth - pnorth;
            double deast = ceast - cnorth;
            double heading = n_Const::c_Convert::dPiO2() - atan2(dnorth, deast);
            double speed = sqrt(dnorth*dnorth + deast*deast)/del_t;

            // note, to estimate average heading, keep track of sin/cos sums
            speed_est += speed;
            cosheading += cos(heading);
            sinheading += sin(heading);
        }

        if(Nsamples > 0)
        {
            double heading_est = atan2(sinheading, cosheading)*n_Const::c_Convert::dRadiansToDegrees();
            projstate->setGroundspeed(speed_est/Nsamples);
            projstate->setCourse(heading_est);
            projstate->setHeading(heading_est);
        }
    }

    // time from sample to now is far enough away in time to linearly project location
    if(dt > 100)
    {
        uxas::common::utilities::FlatEarth flatEarth;
        double north, east;
        flatEarth.ConvertLatLong_degToNorthEast_m(projstate->getLocation()->getLatitude(), projstate->getLocation()->getLongitude(), north, east);
        north += projstate->getGroundspeed()*dt/1000.0*cos( projstate->getCourse() * n_Const::c_Convert::dDegreesToRadians() );
        east += projstate->getGroundspeed()*dt/1000.0*sin( projstate->getCourse() * n_Const::c_Convert::dDegreesToRadians() );
        double lat, lon;
        flatEarth.ConvertNorthEast_mToLatLong_deg(north, east, lat, lon);
        projstate->getLocation()->setLatitude(lat);
        projstate->getLocation()->setLongitude(lon);
    }

    // add to estimated entity log
    // time (ms since 1 Jan 1970), lat (deg), lon (deg), speed (m/s), heading (deg)
    bool addlogheader = false;
    if( !boost::filesystem::exists( m_workDirectoryPath + "/" + "estimated.csv" ) )
        addlogheader = true;

    std::ofstream logfile;
    logfile.open(m_workDirectoryPath + "/" + "estimated.csv", std::ios_base::app);
    if(addlogheader)
        logfile << "# time (ms since 1 Jan 1970), lat (deg), lon (deg), speed (m/s), heading (deg)" << std::endl;
    logfile << entityState->getTime() << ",";
    logfile << projstate->getLocation()->getLatitude() << ",";
    logfile << projstate->getLocation()->getLongitude() << ",";
    logfile << projstate->getGroundspeed() << ",";
    logfile << projstate->getHeading() << std::endl;
    logfile.close();

    // point cameras at the target point
    auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
    vehicleActionCommand->setVehicleID(entityState->getID());
    auto entconfig = m_entityConfigurations.find(entityState->getID());
    if(entconfig != m_entityConfigurations.end())
    {
        for(auto payload : entconfig->second->getPayloadConfigurationList())
        {
            if(afrl::cmasi::isGimbalConfiguration(payload))
            {
                auto gimbal = static_cast<afrl::cmasi::GimbalConfiguration*>(payload);

                // TODO, check to see if lat/lon slaved point mode is allowed
                auto s = new afrl::cmasi::GimbalStareAction;
                s->setPayloadID(gimbal->getPayloadID());
                s->setStarepoint(projstate->getLocation()->clone());
                s->getAssociatedTaskList().push_back(m_task->getTaskID());
                vehicleActionCommand->getVehicleActionList().push_back(s);
            }
        }
    }

    // add the loiter
    auto loiterAction = new afrl::cmasi::LoiterAction();
    loiterAction->setLocation(projstate->getLocation()->clone());
    if (m_entityConfigurations.find(entityState->getID()) != m_entityConfigurations.end())
    {
        loiterAction->getLocation()->setAltitude(m_entityConfigurations[entityState->getID()]->getNominalAltitude());
        loiterAction->getLocation()->setAltitudeType(m_entityConfigurations[entityState->getID()]->getNominalAltitudeType());
        loiterAction->setAirspeed(m_entityConfigurations[entityState->getID()]->getNominalSpeed());
    }
    else
    {
        loiterAction->getLocation()->setAltitude(entityState->getLocation()->getAltitude());
        loiterAction->getLocation()->setAltitudeType(entityState->getLocation()->getAltitudeType());
        loiterAction->setAirspeed(entityState->getGroundspeed());
        CERR_FILE_LINE_MSG("ERROR::Task_WatchTask:: no EntityConfiguration found for Entity[" << entityState->getID() << "]")
    }
    loiterAction->setRadius(m_loiterRadius_m);
    loiterAction->setAxis(0.0);
    loiterAction->setDirection(afrl::cmasi::LoiterDirection::CounterClockwise);
    loiterAction->setDuration(-1.0);
    loiterAction->setLength(0.0);
    loiterAction->setLoiterType(afrl::cmasi::LoiterType::Circular);
    loiterAction->getAssociatedTaskList().push_back(m_task->getTaskID());
    vehicleActionCommand->getVehicleActionList().push_back(loiterAction);
    loiterAction = nullptr; //gave up ownership

    // send out the response
    sendSharedLmcpObjectBroadcastMessage(vehicleActionCommand);
}

} //namespace task
} //namespace service
} //namespace uxas

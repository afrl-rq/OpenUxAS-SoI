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
#include "uxas/messages/task/TaskOption.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <fstream>
#include "boost/filesystem.hpp"

namespace uxas
{
namespace service
{
namespace task
{
OverwatchTaskService::ServiceBase::CreationRegistrar<OverwatchTaskService>
OverwatchTaskService::s_registrar(OverwatchTaskService::s_registryServiceTypeNames());

OverwatchTaskService::OverwatchTaskService()
: DynamicTaskServiceBase(OverwatchTaskService::s_typeName(), OverwatchTaskService::s_directoryName())
{
    m_isMakeTransitionWaypointsActive = true;
}

OverwatchTaskService::~OverwatchTaskService()
{
}

bool
OverwatchTaskService::configureDynamicTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    bool isSuccessful = true;

    if (afrl::impact::isWatchTask(m_task.get()))
    {
        m_watchTask = std::static_pointer_cast<afrl::impact::WatchTask>(m_task);
        if (!m_watchTask)
        {
            UXAS_LOG_ERROR("**OverwatchTaskService::bConfigure failed to cast a WatchTask from the task pointer.");
            isSuccessful = false;
        }
        else
        {
            UXAS_LOG_ERROR("**OverwatchTaskService::bConfigure failed: taskObject[" + m_task->getFullLmcpTypeName() + "] is not a WatchTask.");
            isSuccessful = false;
        }
    }

    if (m_entityStates.find(m_watchTask->getWatchedEntityID()) != m_entityStates.end())
    {
        m_watchedEntityStateLast = m_entityStates[m_watchTask->getWatchedEntityID()];
    }
    else
    {
        UXAS_LOG_ERROR("Overwatch Task ", m_watchTask->getTaskID(), " Watched Entity ID ", m_watchTask->getWatchedEntityID(), " Does Not Exist");
        isSuccessful = false;
    }

    return (isSuccessful);
}

bool
OverwatchTaskService::processRecievedLmcpMessageDynamicTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
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
  
    int64_t optionId(TaskOptionClass::m_firstOptionId);

    return (false); // always false implies never terminating service from here
};


std::shared_ptr<afrl::cmasi::Location3D> OverwatchTaskService::calculateTargetLocation(const std::shared_ptr<afrl::cmasi::EntityState> entityState)
{
    // if no valid watch state, do nothing
    if(!m_watchedEntityStateLast)
    {
        UXAS_LOG_ERROR("Overwatch Task ", "no watchedEntityState found for Entity[", m_watchTask->getWatchedEntityID(), "]");
        return std::shared_ptr<afrl::cmasi::Location3D>();
    }

    // if no watch track is stale, do nothing
    int64_t dt = entityState->getTime() - m_watchedEntityStateLast->getTime();
    if(dt > 15000)
    {
        UXAS_LOG_ERROR("Overwatch Task ", "stale watch state [", m_watchTask->getWatchedEntityID(), "]: ", dt);
        return std::shared_ptr<afrl::cmasi::Location3D>();
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
    return std::shared_ptr<afrl::cmasi::Location3D>(projstate->getLocation()->clone());
}

} //namespace task
} //namespace service
} //namespace uxas

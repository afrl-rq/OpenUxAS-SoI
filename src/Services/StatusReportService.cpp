// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   StatusReportService.cpp
 * Author: derek
 *
 * Created on Jan 30, 2018
 *
 * <Service Type="StatusReportService" VehicleID="100" 
 *                                     ReportPeriod_ms="5000"
 *                                     StaleStateTime_ms="5000"
 *                                     KeepAliveExpiration_ms="7000" />
 *  
 */

#include "StatusReportService.h"
#include "UxAS_TimerManager.h"
#include "uxas/messages/uxnative/EntityJoin.h"
#include "uxas/messages/uxnative/EntityExit.h"
#include "uxas/messages/uxnative/AutopilotKeepAlive.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/EntityStateDescendants.h"

namespace uxas  // uxas::
{
namespace service   // uxas::service::
{

// this entry registers the service in the service creation registry
StatusReportService::ServiceBase::CreationRegistrar<StatusReportService>
StatusReportService::s_registrar(StatusReportService::s_registryServiceTypeNames());

// service constructor
StatusReportService::StatusReportService()
: ServiceBase(StatusReportService::s_typeName(), StatusReportService::s_directoryName())
{
    m_report.setValidState(false);
    m_report.setValidAuthorization(false);
    m_report.setSpeedAuthorization(false);
    m_report.setGimbalAuthorization(false);
};

// service destructor
StatusReportService::~StatusReportService()
{
    // destroy report timer
    uint64_t delayTime_ms{10};
    if (m_reportTimerId && !uxas::common::TimerManager::getInstance().destroyTimer(m_reportTimerId, delayTime_ms))
    {
        UXAS_LOG_WARN("StatusReportService::~StatusReportService failed to destroy report timer "
                "(m_reportTimerId) with timer ID ", m_reportTimerId, " within ", delayTime_ms, " millisecond timeout");
    }
    
    // destroy keep alive timer
    if (m_keepAliveTimerId && !uxas::common::TimerManager::getInstance().destroyTimer(m_keepAliveTimerId, delayTime_ms))
    {
        UXAS_LOG_WARN("StatusReportService::~StatusReportService failed to destroy keep alive gap timer "
                "(m_keepAliveTimerId) with timer ID ", m_keepAliveTimerId, " within ", delayTime_ms, " millisecond timeout");
    }
    
    // destroy stale state timer
    if (m_staleStateTimerId && !uxas::common::TimerManager::getInstance().destroyTimer(m_staleStateTimerId, delayTime_ms))
    {
        UXAS_LOG_WARN("StatusReportService::~StatusReportService failed to destroy keep alive gap timer "
                "(m_staleStateTimerId) with timer ID ", m_staleStateTimerId, " within ", delayTime_ms, " millisecond timeout");
    }
};

bool StatusReportService::configure(const pugi::xml_node& ndComponent)
{
    // default to entity identified in top-level configuration
    m_vehicleId = ndComponent.attribute("VehicleID").as_int64(m_entityId);
    m_report.setVehicleID(m_vehicleId);
    
    // make sure report period is something sane (e.g. at most 10Hz)
    m_reportPeriod_ms = ndComponent.attribute("ReportPeriod_ms").as_uint(m_reportPeriod_ms);
    if(m_reportPeriod_ms < 100) m_reportPeriod_ms = 100;
    
    // make sure state timeout is something sane (e.g. at most 100Hz)
    m_staleStateTime_ms = ndComponent.attribute("StaleStateTime_ms").as_uint(m_staleStateTime_ms); 
    if(m_staleStateTime_ms < 10) m_staleStateTime_ms = 10;
    
    // make sure keep-alive timeout is something sane (e.g. at least 1 sec)
    m_keepAliveExpirationTime_ms = ndComponent.attribute("KeepAliveExpiration_ms").as_uint(m_keepAliveExpirationTime_ms); 
    if(m_keepAliveExpirationTime_ms < 1000) m_keepAliveExpirationTime_ms = 1000;
    
    // subscribe to join, exit, and keep-alive messages
    addSubscriptionAddress(uxas::messages::uxnative::EntityJoin::Subscription);
    addSubscriptionAddress(uxas::messages::uxnative::EntityExit::Subscription);
    addSubscriptionAddress(uxas::messages::uxnative::AutopilotKeepAlive::Subscription);
    
    // track all entity states
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);

    return (true);
}

bool StatusReportService::initialize()
{
    // create report timer
    m_reportTimerId = uxas::common::TimerManager::getInstance().createTimer(
        std::bind(&StatusReportService::OnReportTimeout, this),
        "StatusReportService::OnReportTimeout");
    
    // create keep alive timer
    m_keepAliveTimerId = uxas::common::TimerManager::getInstance().createTimer(
        std::bind(&StatusReportService::OnKeepAliveTimeout, this), 
        "StatusReportService::OnKeepAliveTimeout");
    
    // create stale state timer
    m_staleStateTimerId = uxas::common::TimerManager::getInstance().createTimer(
        std::bind(&StatusReportService::OnStaleStateTimeout, this), 
        "StatusReportService::OnStaleStateTimeout");
    
    return (true);
}

bool StatusReportService::start()
{
    // start periodic reporting timer
    uxas::common::TimerManager::getInstance().startPeriodicTimer(m_reportTimerId, m_reportPeriod_ms, m_reportPeriod_ms);
    return (true);
}

bool StatusReportService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    // lock during report update
    std::unique_lock<std::mutex> lock(m_mutex);
    
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState> (receivedLmcpMessage->m_object);
    if(entityState && m_vehicleId == entityState->getID())
    {
        m_report.setVehicleTime(entityState->getTime());
        m_report.getCurrentTaskList() = entityState->getAssociatedTasks();
        m_report.setValidState(true);
        
        // reset timer to detect stale state (fresh now, timeout indicates stale)
        uxas::common::TimerManager::getInstance().startSingleShotTimer(m_staleStateTimerId, m_staleStateTime_ms);
        
        if(!uxas::common::TimerManager::getInstance().isTimerActive(m_reportTimerId))
        {
            // start periodic reporting timer
            uxas::common::TimerManager::getInstance().startPeriodicTimer(m_reportTimerId, m_reportPeriod_ms, m_reportPeriod_ms);
        }
    }
    else if(uxas::messages::uxnative::isEntityJoin(receivedLmcpMessage->m_object))
    {
        auto joinmsg = std::static_pointer_cast<uxas::messages::uxnative::EntityJoin>(receivedLmcpMessage->m_object);
        m_connections.insert(joinmsg->getEntityID());
        m_report.getConnectedEntities().clear();
        m_report.getConnectedEntities().insert(m_report.getConnectedEntities().end(), m_connections.begin(), m_connections.end());
    }
    else if(uxas::messages::uxnative::isEntityExit(receivedLmcpMessage->m_object))
    {
        auto exitmsg = std::static_pointer_cast<uxas::messages::uxnative::EntityExit>(receivedLmcpMessage->m_object);
        m_connections.erase(exitmsg->getEntityID());
        m_report.getConnectedEntities().clear();
        m_report.getConnectedEntities().insert(m_report.getConnectedEntities().end(), m_connections.begin(), m_connections.end());
    }
    else if (uxas::messages::uxnative::isAutopilotKeepAlive(receivedLmcpMessage->m_object.get()))
    {
        auto keepAlive = std::static_pointer_cast<uxas::messages::uxnative::AutopilotKeepAlive>(receivedLmcpMessage->m_object);
        m_report.setValidAuthorization(keepAlive->getAutopilotEnabled());
        m_report.setSpeedAuthorization(keepAlive->getSpeedAuthorized());
        m_report.setGimbalAuthorization(keepAlive->getGimbalEnabled());        
        // reset timer to determine loss of keep-alive stream
        uxas::common::TimerManager::getInstance().startSingleShotTimer(m_keepAliveTimerId, m_keepAliveExpirationTime_ms);
    }
    
    return (false); // always return false unless terminating
}

void StatusReportService::OnReportTimeout()
{
    std::unique_lock<std::mutex> lock(m_mutex);
    std::shared_ptr<uxas::messages::uxnative::OnboardStatusReport>
        sendReport(m_report.clone());
    lock.unlock();
    sendSharedLmcpObjectBroadcastMessage(sendReport);
}

void StatusReportService::OnKeepAliveTimeout()
{
    std::unique_lock<std::mutex> lock(m_mutex);
    m_report.setValidAuthorization(false);
    m_report.setSpeedAuthorization(false);
    m_report.setGimbalAuthorization(false);
}

void StatusReportService::OnStaleStateTimeout()
{
    std::unique_lock<std::mutex> lock(m_mutex);
    m_report.setValidState(false);
}

}; //namespace service
}; //namespace uxas

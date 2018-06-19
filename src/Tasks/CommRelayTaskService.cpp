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
#include "afrl/vehicles/GroundVehicleConfiguration.h"
#include "afrl/vehicles/SurfaceVehicleConfiguration.h"
#include "afrl/impact/RadioTowerConfiguration.h"
#include "afrl/impact/RadioTowerState.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"


#include "Constants/Convert.h"
#include "DpssDataTypes.h"
#include "TimeUtilities.h"

#include <sstream>      //std::stringstream



namespace uxas
{
namespace service
{
namespace task
{
CommRelayTaskService::ServiceBase::CreationRegistrar<CommRelayTaskService>
CommRelayTaskService::s_registrar(CommRelayTaskService::s_registryServiceTypeNames());

CommRelayTaskService::CommRelayTaskService()
: DynamicTaskServiceBase(CommRelayTaskService::s_typeName(), CommRelayTaskService::s_directoryName())
{
};

CommRelayTaskService::~CommRelayTaskService()
{
};

bool
CommRelayTaskService::configureDynamicTask(const pugi::xml_node& ndComponent)

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
                UXAS_LOG_ERROR("**CommRelayTaskService::bConfigure failed to cast a CommRelayTask from the task pointer.");
                isSuccessful = false;
            }
        }
        else
        {
            UXAS_LOG_ERROR("**CommRelayTaskService::bConfigure failed: taskObject[" + m_task->getFullLmcpTypeName() + "] is not a CommRelayTask.");
            isSuccessful = false;
        }
    } //isSuccessful
    if (isSuccessful)
    {
        if (m_CommRelayTask->getSupportedEntityID() == 0)
        {
            if (m_CommRelayTask->getDestinationLocation() != nullptr)
            {
                m_supportedEntityStateLast = std::shared_ptr<afrl::cmasi::Location3D>(m_CommRelayTask->getDestinationLocation()->clone());
            }
        }
        else
        {
            if (m_entityStates.find(m_CommRelayTask->getSupportedEntityID()) != m_entityStates.end())
            {
                m_supportedEntityStateLast = std::shared_ptr<afrl::cmasi::Location3D>(m_entityStates[m_CommRelayTask->getSupportedEntityID()]->getLocation()->clone());
            }
            else
            {
                UXAS_LOG_ERROR("**CommRelayTaskService: supportedEntityID ", m_CommRelayTask->getSupportedEntityID(), " does not exist");
                isSuccessful = false;
            }
        }

        auto towerId = m_CommRelayTask->getTowerID();
        if (m_entityStates.find(towerId) == m_entityStates.end())
        {
            UXAS_LOG_ERROR("**CommRelayTaskService: tower with ID ", towerId, " does not exist");
            isSuccessful = false;
        }

        if (m_entityConfigurations.find(towerId) != m_entityConfigurations.end())
        {
            if (!afrl::impact::isRadioTowerConfiguration(m_entityConfigurations[towerId].get()))
            {
                UXAS_LOG_ERROR("**CommRelayTaskService: entity  config with ID ", towerId, " is not a radio tower");
                isSuccessful = false;
            }
        }
        else
        {
            UXAS_LOG_ERROR("CommRelayTaskService: radio tower ID ", towerId, " does not exist");
            isSuccessful = false;
        }

    } //if(isSuccessful)

    return (isSuccessful);
}

bool
CommRelayTaskService::processRecievedLmcpMessageDynamicTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpObject);
    if (entityState)
    {
        if (entityState->getID() == m_CommRelayTask->getSupportedEntityID())
        {
            m_supportedEntityStateLast = std::shared_ptr<afrl::cmasi::Location3D>(entityState->getLocation()->clone());
        }
    }
    return (false); // always false implies never terminating service from here
};

std::shared_ptr<afrl::cmasi::Location3D> CommRelayTaskService::calculateTargetLocation(const std::shared_ptr<afrl::cmasi::EntityState> entityState)
{
    auto middle = std::shared_ptr<afrl::cmasi::Location3D>(entityState->getLocation()->clone());
    int64_t optionId(TaskOptionClass::m_firstOptionId);
    if (m_supportedEntityStateLast)
    {
        // look up speed to use for commanding vehicle
        double alt = entityState->getLocation()->getAltitude();
        if (m_entityConfigurations.find(entityState->getID()) != m_entityConfigurations.end())
        {
            alt = m_entityConfigurations[entityState->getID()]->getNominalAltitude();
        }

        moveToHalfWayPoint(middle);
        middle->setAltitude(alt);

    }
    return middle;
}

void CommRelayTaskService::moveToHalfWayPoint(const std::shared_ptr<afrl::cmasi::Location3D>& supportedEntityStateLocation)
{

    // extract location of tower
    int64_t towerId = m_CommRelayTask->getTowerID();
    std::shared_ptr<afrl::cmasi::Location3D> towerLocation{ nullptr };
    if (m_entityStates.find(towerId) != m_entityStates.end())
    {
        towerLocation.reset(m_entityStates[towerId]->getLocation()->clone());
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
        flatEarth.ConvertLatLong_degToNorthEast_m(m_supportedEntityStateLast->getLatitude(), m_supportedEntityStateLast->getLongitude(), north, east);
        Dpss_Data_n::xyPoint target(east, north);

        // go halfway between 'targetLocation' and 'tower' TODO: make this more efficient?
        target.x = (tower.x + target.x) / 2;
        target.y = (tower.y + target.y) / 2;

        // back to lat/lon
        double lat, lon;
        flatEarth.ConvertNorthEast_mToLatLong_deg(target.y, target.x, lat, lon);

        supportedEntityStateLocation->setLatitude(lat);
        supportedEntityStateLocation->setLongitude(lon);
}

}; //namespace task
}; //namespace service
}; //namespace uxas

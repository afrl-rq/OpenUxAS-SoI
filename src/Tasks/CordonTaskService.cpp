// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_CordonTask.cpp
 * Author: derek
 * 
 * Created on March 7, 2016, 4:44 PM
 */


#include "CordonTaskService.h"

#include "Position.h"
#include "FileSystemUtilities.h"

#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/route/ROUTE.h"
#include "uxas/messages/route/RouteConstraints.h"
#include "uxas/messages/route/EgressRouteRequest.h"
#include "uxas/messages/route/EgressRouteResponse.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"
#include "Permute.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <iomanip>  //setfill

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "CRDT-CRDT-CRDT-CRDT:: CordonTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "CRDT-CRDT-CRDT-CRDT:: CordonTask:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();

// functor called for each permutation

class f
{
    std::string& m_compositionString;
    std::vector<int64_t>& m_vehicleIds;
    std::vector<int64_t>& m_locationIds;
    std::unordered_map<std::pair<int64_t, int64_t>, int64_t, uxas::service::task::CordonTaskService::PairHashInt64>& m_optionIdMap;
    bool m_isVehicleConstrained{false};

public:

    explicit f(std::vector<int64_t>& vehicleIds, std::vector<int64_t>& locationIds, std::string& compositionString, bool isVehicleConstrained,
               std::unordered_map<std::pair<int64_t, int64_t>, int64_t, uxas::service::task::CordonTaskService::PairHashInt64>& optionIdMap)
    : m_compositionString(compositionString), m_vehicleIds(vehicleIds), m_locationIds(locationIds), m_optionIdMap(optionIdMap), m_isVehicleConstrained(isVehicleConstrained) { }

    template <class It>
    bool operator()(It first, It last) // called for each permutation
    {
        if (first != last)
        {
            m_compositionString += " .(";
            size_t index = 0;
            for (; first != last; first++) // loop over vehicle (or location) IDs in permutation
            {
                if (m_isVehicleConstrained)
                {
                    if (index < m_vehicleIds.size())
                    {
                        auto optionEntry = m_optionIdMap.find(std::make_pair(m_vehicleIds[index], *first));
                        if (optionEntry != m_optionIdMap.end())
                        {
                            std::string optionId = std::to_string(optionEntry->second);
                            m_compositionString += "p" + optionId + " ";
                        }
                        else
                        {
                            //ERROR
                            CERR_FILE_LINE_MSG(" No option ID found for the following vehicle, node pair: " << m_vehicleIds[index] << ", " << *first)
                        }
                    }
                    else
                    {
                        //ERROR
                        CERR_FILE_LINE_MSG(" Unable to find vehicle ID in eligible vehicle list for index " << index)
                    }
                }
                else
                {
                    if (index < m_locationIds.size())
                    {
                        auto optionEntry = m_optionIdMap.find(std::make_pair(*first, m_locationIds[index]));
                        if (optionEntry != m_optionIdMap.end())
                        {
                            std::string optionId = std::to_string(optionEntry->second);
                            m_compositionString += "p" + optionId + " ";
                        }
                        else
                        {
                            //ERROR
                            CERR_FILE_LINE_MSG(" No option ID found for the following vehicle, node pair: " << *first << "," << m_locationIds[index])
                        }
                    }
                    else
                    {
                        //ERROR
                        CERR_FILE_LINE_MSG(" Unable to find location ID in eligible location list for index " << index)
                    }
                }
                index++;
            }
            m_compositionString += ")";
        }
        return false;
    }
};


namespace uxas
{
namespace service
{
namespace task
{
CordonTaskService::ServiceBase::CreationRegistrar<CordonTaskService>
CordonTaskService::s_registrar(CordonTaskService::s_registryServiceTypeNames());

CordonTaskService::CordonTaskService()
: TaskServiceBase(CordonTaskService::s_typeName(), CordonTaskService::s_directoryName()) { };

CordonTaskService::~CordonTaskService() { };

bool
CordonTaskService::configureTask(const pugi::xml_node& ndComponent)

{
    std::string strBasePath = m_workDirectoryPath;
    std::stringstream sstrErrors;


    bool isSuccessful(true);

    if (isSuccessful)
    {
        if (afrl::impact::isCordonTask(m_task.get()))
        {
            m_cordonTask = std::static_pointer_cast<afrl::impact::CordonTask>(m_task);
            if (!m_cordonTask)
            {
                sstrErrors << "ERROR:: **CordonTaskService::bConfigure failed to cast a CordonTask from the task pointer." << std::endl;
                CERR_FILE_LINE_MSG(sstrErrors.str())
                isSuccessful = false;
            }
        }
        else
        {
            sstrErrors << "ERROR:: **CordonTaskService::bConfigure failed: taskObject[" << m_task->getFullLmcpTypeName() << "] is not a CordonTask." << std::endl;
            CERR_FILE_LINE_MSG(sstrErrors.str())
            isSuccessful = false;
        }
    } //isSuccessful

    addSubscriptionAddress(uxas::messages::route::EgressRouteResponse::Subscription);
    addSubscriptionAddress(uxas::messages::route::RouteResponse::Subscription);

    return (isSuccessful);
}

/*
 * - Process and store every EntityConfiguration and EntityState message received.
 * 
 * If this task is included in an AutomationRequest then:
 * 1) request sensor footprint parameters,SensorFootprintRequest, for each
 *    eligible vehicle using : GSD, view elevations, and nominal altitude
 * 2) For all sensor footprints, returned in the SensorFootprintResponse,
 *    build route constraints and send a "cost only" RoutePlanRequest.
 * 3) Construct and send TaskPlanOptions, this includes the options, an ID,
 *    and a composition string
 * 4) On receipt of a TaskImplementationRequest, construct and send a 
 *    RoutePlanRequest to construct the waypoint plan for the task
 * 5) Construct, and send, TaskImplementationResponse after receiving a 
 *    RouteResponse
 * 
 * 
 *   -AutomationRequest
 *  - GET SENSOR FOOTPRINTS
 *   -SensorFootprintRequest
 *   -SensorFootprintResponse
 *  - CONSTRUCT AN OPTION FOR EACH FOOTPRINT
 *   - RoutPlanRequest
 *   - RoutPlanResponse
 *   - TaskPlanOptions
 *  - TASK IMPLEMENTATION
 *   - TaskImplementationRequest
 *   - RouteRequest
 *   - RouteResponse
 *   - TaskImplementationResponse
 *  - VEHICLE STATE UPDATE
 *   - CameraAction (? set camera for gimble angle and FOV (ZOOM) ?)
 *   - VehicleActionCommand (? point camera ?)
 */



bool
CordonTaskService::processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpObject))
{
    std::stringstream sstrError;
    if (m_idVsUniqueAutomationRequest.find(m_latestUniqueAutomationRequestId) == m_idVsUniqueAutomationRequest.end())
    {
        //TODO:: "warning received uniqueAutomationResponse[",m_latestUniqueAutomationRequestId,"] with no corresponding uniqueAutomationRequest"
    }
    else
    {
        auto currentAutomationRequest = m_idVsUniqueAutomationRequest[m_latestUniqueAutomationRequestId];
        if (uxas::messages::route::isEgressRouteResponse(receivedLmcpObject))
        {
            auto egressRouteResponse = std::static_pointer_cast<uxas::messages::route::EgressRouteResponse>(receivedLmcpObject);
            if (egressRouteResponse->getResponseID() == m_task->getTaskID())
            {
                // set/reset task plan options
                m_taskPlanOptions->setTaskID(m_task->getTaskID());
                m_optionIdVsTaskOptionClass.clear();

                int64_t locationId = 1;
                int64_t optionId = TaskOptionClass::m_firstOptionId;
                std::vector<int64_t> locationIds;
                for (auto& location : egressRouteResponse->getNodeLocations())
                {
                    for (auto itEligibleEntities = m_speedAltitudeVsEligibleEntityIdsRequested.begin(); itEligibleEntities != m_speedAltitudeVsEligibleEntityIdsRequested.end(); itEligibleEntities++)
                    {
                        calculateOption(itEligibleEntities->second, location, locationId, optionId);
                    }
                    locationIds.push_back(locationId);
                    locationId++;
                }

                // calculate composition string
                std::string compositionString = calculateCompositionString(locationIds, currentAutomationRequest->getOriginalRequest()->getEntityList());
                m_taskPlanOptions->setComposition(compositionString);
                std::shared_ptr<avtas::lmcp::Object> pOptions = std::static_pointer_cast<avtas::lmcp::Object>(m_taskPlanOptions);
                sendSharedLmcpObjectBroadcastMessage(pOptions);
            }
        }
    }
    return (false); // always false implies never terminating service from here
};

std::string CordonTaskService::calculateCompositionString(std::vector<int64_t>& locationIds, std::vector<int64_t>& vehicleIds)
{
    std::string compositionString = "";
    int64_t N = locationIds.size();
    int64_t K = vehicleIds.size();
    compositionString = "+(";
    if (K > N)
    {
        for_each_permutation<std::vector<int64_t>::iterator, f>(vehicleIds.begin(), vehicleIds.begin() + N, vehicleIds.end(), f(vehicleIds, locationIds, compositionString, false, m_vehicleIdNodeIdVsOptionId));
    }
    else
    {
        for_each_permutation<std::vector<int64_t>::iterator, f>(locationIds.begin(), locationIds.begin() + K, locationIds.end(), f(vehicleIds, locationIds, compositionString, true, m_vehicleIdNodeIdVsOptionId));
    }
    compositionString += ")";

    //std::vector< std::vector< std::pair<int64_t, int64_t> > > allCombinations;
    //for_each_permutation<std::vector<int64_t>::iterator, f>(locationIds.begin(), locationIds.begin() + (K + 1), locationIds.end(), f(allCombinations));

    return compositionString;
}

void CordonTaskService::buildTaskPlanOptions()
{
    // build an 'egress route request' from the ground planner (external)
    auto egressRequest = std::shared_ptr<uxas::messages::route::EgressRouteRequest>(new uxas::messages::route::EgressRouteRequest);
    egressRequest->setRequestID(m_cordonTask->getTaskID());
    egressRequest->setStartLocation(m_cordonTask->getCordonLocation()->clone());
    egressRequest->setRadius(m_cordonTask->getStandoffDistance());
    std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(egressRequest);
    sendSharedLmcpObjectBroadcastMessage(pRequest);
};

void CordonTaskService::calculateOption(const std::vector<int64_t>& eligibleEntities,
                                        afrl::cmasi::Location3D* location, int64_t& locationId, int64_t& optionId)
{
    for (auto itEntity = eligibleEntities.begin(); itEntity != eligibleEntities.end(); itEntity++)
    {
        // One Entity per option
        auto taskOption = new uxas::messages::task::TaskOption;
        taskOption->setTaskID(m_task->getTaskID());
        taskOption->setOptionID(optionId);
        taskOption->getEligibleEntities().clear();
        taskOption->getEligibleEntities().push_back(*itEntity); // defaults to all entities eligible
        taskOption->setStartLocation(location->clone());
        taskOption->setStartHeading(0.0); // TODO: use heading from egress route response
        taskOption->setEndLocation(location->clone());
        taskOption->setEndHeading(0.0);
        auto pTaskOption = std::shared_ptr<uxas::messages::task::TaskOption>(taskOption->clone());
        m_optionIdVsTaskOptionClass.insert(std::make_pair(optionId, std::make_shared<TaskOptionClass>(pTaskOption)));
        m_taskPlanOptions->getOptions().push_back(taskOption);

        // update map of vehicle option id
        m_vehicleIdNodeIdVsOptionId.insert(std::make_pair(std::make_pair(*itEntity, locationId), optionId));
        optionId++;
    }
};

}; //namespace task
}; //namespace service
}; //namespace uxas

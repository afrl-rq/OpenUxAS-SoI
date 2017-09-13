// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_BatchSummary.cpp
 * Author: derek
 * 
 * Created on Oct 25, 2015, 3:56 PM
 */

#include "BatchSummaryService.h"

#include "UxAS_Log.h"
#include "UnitConversions.h"
#include "Permute.h"

#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/TaskDescendants.h"     

#include "afrl/vehicles/VEHICLES.h"

#include <map>
#include <numeric>
#include <uxas/messages/task/TaskPlanOptions.h>

#define STRING_COMPONENT_NAME "BatchSummary"
#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME
#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"
#define STRING_XML_FAST_PLAN "FastPlan"
#define STRING_XML_LANE_SPACING "LaneSpacing"

// functor called for each permutation

class f
{
    afrl::impact::TaskSummary* tsum;
    afrl::impact::TaskSummary* orig;
    std::shared_ptr<afrl::impact::BatchSummaryResponse>& response;
    std::vector<std::shared_ptr<afrl::impact::VehicleSummary> >& vehicles;
public:

    explicit f(afrl::impact::TaskSummary* t,
        std::vector<std::shared_ptr<afrl::impact::VehicleSummary> >& v,
        std::shared_ptr<afrl::impact::BatchSummaryResponse>& r) : tsum(nullptr), orig(t), vehicles(v), response(r)
    {
    }

    template <class It>
    bool operator()(It first, It last) // called for each permutation
    {
        if (first != last)
        {
            tsum = orig->clone();
            for (; first != last; first++)
            {
                tsum->getPerformingVehicles().push_back(vehicles.at(*first)->clone());
            }
            response->getSummaries().push_back(tsum);
            tsum = nullptr;
        }
        return false;
    }
};

namespace uxas
{
    namespace service
    {
        BatchSummaryService::ServiceBase::CreationRegistrar<BatchSummaryService>
            BatchSummaryService::s_registrar(BatchSummaryService::s_registryServiceTypeNames());

        BatchSummaryService::BatchSummaryService()
            : ServiceBase(BatchSummaryService::s_typeName(), BatchSummaryService::s_directoryName())
        {
        };

        BatchSummaryService::~BatchSummaryService()
        {
        };

        bool
            BatchSummaryService::initialize()
        {

            return true;
        }

        bool
            BatchSummaryService::configure(const pugi::xml_node & ndComponent)

        {
            std::string strBasePath = m_workDirectoryPath;
            uint32_t ui32EntityID = m_entityId;
            uint32_t ui32LmcpMessageSize_max = 100000;
            std::stringstream sstrErrors;

            std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();

            std::string strFastPlan = ndComponent.attribute(STRING_XML_FAST_PLAN).value();
            if (!strFastPlan.empty())
            {
                m_fastPlan = ndComponent.attribute(STRING_XML_FAST_PLAN).as_bool();
            }

            // track states for watch task location prediction
            addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
            addSubscriptionAddress(afrl::impact::RadioTowerConfiguration::Subscription);
            addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
            addSubscriptionAddress(afrl::vehicles::GroundVehicleConfiguration::Subscription);
            addSubscriptionAddress(afrl::vehicles::SurfaceVehicleConfiguration::Subscription);
            addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
            addSubscriptionAddress(afrl::impact::RadioTowerState::Subscription);
            addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
            addSubscriptionAddress(afrl::vehicles::GroundVehicleState::Subscription);
            addSubscriptionAddress(afrl::vehicles::SurfaceVehicleState::Subscription);

            // Tasks which are handled by this planner
            // track all tasks
#define SUBSCRIBE_TO_TASKS
#include "00_ServiceList.h"

            addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);//assume all KOZs apply to all vehicles

                                                                           // Primary messages for actual route construction
            addSubscriptionAddress(afrl::impact::BatchSummaryRequest::Subscription);
            addSubscriptionAddress(messages::task::TaskAutomationResponse::Subscription);
            addSubscriptionAddress(messages::route::EgressRouteResponse::Subscription);
            addSubscriptionAddress(uxas::messages::task::TaskPlanOptions::Subscription);

            return true; // may not have the proper fast plan value, but proceed anyway
        }

        bool
            BatchSummaryService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
            //example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
        {

            if (uxas::messages::route::isEgressRouteResponse(receivedLmcpMessage->m_object.get()))
            {
                HandleEgressRouteResponse(std::static_pointer_cast<uxas::messages::route::EgressRouteResponse>(receivedLmcpMessage->m_object));
            }
            else if (afrl::impact::isCordonTask(receivedLmcpMessage->m_object.get()) ||
                afrl::impact::isMultiVehicleWatchTask(receivedLmcpMessage->m_object.get()) ||
                afrl::impact::isBlockadeTask(receivedLmcpMessage->m_object.get()))
            {
                auto task = std::static_pointer_cast<afrl::cmasi::Task>(receivedLmcpMessage->m_object);
                m_multiVehicleTasks[task->getTaskID()] = task;
            }
            else if (afrl::impact::isBatchSummaryRequest(receivedLmcpMessage->m_object.get()))
            {
                HandleBatchSummaryRequest(std::static_pointer_cast<afrl::impact::BatchSummaryRequest>(receivedLmcpMessage->m_object));
            }
            else if (std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object))
            {
                auto config = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
                int64_t id = config->getID();
                m_entityConfigs[id] = config;

                if (afrl::impact::isRadioTowerConfiguration(receivedLmcpMessage->m_object.get()))
                {
                    auto rconfig = std::static_pointer_cast<afrl::impact::RadioTowerConfiguration>(receivedLmcpMessage->m_object);
                    int64_t id = rconfig->getID();
                    m_towerLocations[id] = std::shared_ptr<afrl::cmasi::Location3D>(rconfig->getPosition()->clone());
                    m_towerRanges[id] = std::make_pair(rconfig->getRange(), rconfig->getEnabled());
                }
            }
            else if (afrl::cmasi::isEntityState(receivedLmcpMessage->m_object.get()))
            {
                int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
                m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
            }
            else if (afrl::impact::isRadioTowerState(receivedLmcpMessage->m_object.get()))
            {
                int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
                m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
                m_towerLocations[id] = std::shared_ptr<afrl::cmasi::Location3D>(m_entityStates[id]->getLocation()->clone());
                auto rs = std::static_pointer_cast<afrl::impact::RadioTowerState>(receivedLmcpMessage->m_object);
                if (m_towerRanges.find(id) != m_towerRanges.end())
                {
                    m_towerRanges[id].second = rs->getEnabled();
                }
            }
            else if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object.get()))
            {
                int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
                m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
                m_airVehicles.insert(id);
            }
            else if (afrl::vehicles::isGroundVehicleState(receivedLmcpMessage->m_object.get()))
            {
                int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
                m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
                m_groundVehicles.insert(id);
            }
            else if (afrl::vehicles::isSurfaceVehicleState(receivedLmcpMessage->m_object.get()))
            {
                int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
                m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
                m_surfaceVehicles.insert(id);
            }
            else if (uxas::messages::task::isTaskPlanOptions(receivedLmcpMessage->m_object.get()))
            {
                auto taskOptions = std::static_pointer_cast<uxas::messages::task::TaskPlanOptions>(receivedLmcpMessage->m_object);
                for (auto option : taskOptions->getOptions()) {
                    m_taskLengths[taskOptions->getTaskID()][option->getOptionID()] = option->getCost();
                }
            }

            else if (messages::task::isTaskAutomationResponse(receivedLmcpMessage->m_object))
            {

                HandleTaskAutomationResponse(std::static_pointer_cast<messages::task::TaskAutomationResponse>(receivedLmcpMessage->m_object));
                //check if all have been received and send out the batchSumaryResponse.
            }
            else if (afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object))
            {
                auto koz = std::static_pointer_cast<afrl::cmasi::KeepOutZone>(receivedLmcpMessage->m_object);
                auto poly = FromAbstractGeometry(koz->getBoundary());

                m_keepOutZones[koz->getZoneID()] = poly;
            }
            return (false); // always false implies never terminating service from here
        }

        void BatchSummaryService::HandleTaskAutomationResponse(const std::shared_ptr<messages::task::TaskAutomationResponse>& object)
        {
            m_workingTaskAutomationResponses[object->getResponseID()] = object; //may be the last one for a BatchSummaryResponse

            auto taskAutomationRequest = m_pendingTaskAutomationRequests.find(object->getResponseID());
            IMPACT_INFORM("recieved internal task automation response ", taskAutomationRequest->second->getRequestID());

            std::list<int64_t> finishedIds;
            for (auto batchSummaryRequestId : m_batchSummaryRequestVsTaskAutomation)
            {
                bool finished = true;
                for (auto expectedTaskAutomationResponse : batchSummaryRequestId.second)
                {
                    if (m_workingTaskAutomationResponses.find(expectedTaskAutomationResponse) == m_workingTaskAutomationResponses.end())
                        finished = false;
                    if (expectedTaskAutomationResponse == object->getResponseID())
                    {
                        auto response = m_workingResponse.find(batchSummaryRequestId.first);
                        //find corresponding summary
                        auto taskSummary = std::find_if(response->second->getSummaries().begin(), response->second->getSummaries().end(), [&](const afrl::impact::TaskSummary* x) { return x->getTaskID() == taskAutomationRequest->second->getOriginalRequest()->getTaskList().front(); });
                        if (taskSummary != response->second->getSummaries().end())
                        {
                            auto vehicleSummary = std::find_if((*taskSummary)->getPerformingVehicles().begin(), (*taskSummary)->getPerformingVehicles().end(), [&](const afrl::impact::VehicleSummary* x) {return x->getVehicleID() == taskAutomationRequest->second->getOriginalRequest()->getEntityList().front(); });
                            if (vehicleSummary != (*taskSummary)->getPerformingVehicles().end())
                            {
                                if (object->getOriginalResponse()->getMissionCommandList().empty())
                                {
                                    continue;
                                }

                                auto waypoints = object->getOriginalResponse()->getMissionCommandList().front()->getWaypointList();
                                UpdateSummaryUtil(*vehicleSummary, waypoints);
                                UpdateSummary(*vehicleSummary, waypoints);
                            }
                        }


                        m_pendingTaskAutomationRequests.erase(object->getResponseID());

                    }
                }
                if (finished)
                {
                    finishedIds.push_back(batchSummaryRequestId.first);

                    for (auto expectedTaskAutomationResponse : batchSummaryRequestId.second)
                    {
                        m_workingTaskAutomationResponses.erase(expectedTaskAutomationResponse);
                    }
                }
            }
            for (auto finishedId : finishedIds)
            {
                //the batchSummaryResponse should be good to go, send it and remove everything
                FinalizeBatchRequest(finishedId);
                m_batchSummaryRequestVsTaskAutomation.erase(finishedId);
            }
        }

        void BatchSummaryService::HandleEgressRouteResponse(std::shared_ptr<uxas::messages::route::EgressRouteResponse> egress)
        {
            // ASSUME: receive back in order sent, FUTURE: add request/response IDs

            bool found = false;
            for (auto workingResponse = m_pendingTaskAutomationRequests.begin(); workingResponse != m_pendingTaskAutomationRequests.end(); workingResponse++)
            {
                //can only match tasks
                auto tasks = workingResponse->second->getOriginalRequest()->getTaskList();
                if (std::find(tasks.begin(), tasks.end(), egress->getResponseID()) != tasks.end())
                {
                    found = true;
                }
            }
            if (!found)
            {
                return; //not for a this. TODO: make sure it is really not for this 
            }

            m_egressPoints[egress->getResponseID()] = egress;
            //}
        }

        bool BatchSummaryService::FinalizeBatchRequest(int64_t responseId)
        {
            // this function is only called when the summaries have been composed
            // only need to check for possible 'best efforts' regarding the tasks in the
            // current summary list

            if (m_workingResponse.find(responseId) == m_workingResponse.end())
                return false;
            auto resp = m_workingResponse[responseId];


            // at this point everything expected has been received, re-build summaries for multi-vehicle tasks
            auto cleanResp = std::shared_ptr<afrl::impact::BatchSummaryResponse>(new afrl::impact::BatchSummaryResponse);
            cleanResp->setResponseID(resp->getResponseID());
            // add single vehicle task summaries and create list of multi-vehicle tasks to reason over
            std::unordered_map<int64_t, std::vector<std::shared_ptr<afrl::impact::VehicleSummary> > > summariesByTask;

            for (auto s : resp->getSummaries())
            {
                int64_t taskId = s->getTaskID();
                //sort
                std::sort(s->getPerformingVehicles().begin(), s->getPerformingVehicles().end(), [](const afrl::impact::VehicleSummary* x, const afrl::impact::VehicleSummary* y) { return x->getVehicleID() < y->getVehicleID(); });
                if (m_multiVehicleTasks.find(taskId) == m_multiVehicleTasks.end())
                {
                    // copy over the summary if it's a single vehicle task
                    cleanResp->getSummaries().push_back(s->clone());
                }
                else
                {
                    // otherwise, add this task to the list of tasks to present as multi-vehicle
                    for (auto v : s->getPerformingVehicles())
                    {
                        summariesByTask[taskId].push_back(std::shared_ptr<afrl::impact::VehicleSummary>(v->clone()));
                    }
                }
            }


            // multi-vehicle tasks include [cordon, multi-overwatch, blockade] only
            for (auto t : summariesByTask)
            {
                if (m_multiVehicleTasks.find(t.first) != m_multiVehicleTasks.end())
                {
                    if (afrl::impact::isCordonTask(m_multiVehicleTasks[t.first].get()))
                    {
                        // the egress points should exist here (checked earlier)
                        if (m_egressPoints.find(t.first) != m_egressPoints.end())
                        {
                            int64_t N = m_egressPoints[t.first]->getNodeLocations().size();
                            BuildSummaryOptions(t.first, cleanResp, t.second, N);
                        }
                    }
                    else if (afrl::impact::isBlockadeTask(m_multiVehicleTasks[t.first].get()))
                    {
                        auto blockTask = std::static_pointer_cast<afrl::impact::BlockadeTask>(m_multiVehicleTasks[t.first]);
                        int64_t N = blockTask->getNumberVehicles();
                        BuildSummaryOptions(t.first, cleanResp, t.second, N);
                    }
                    else if (afrl::impact::isMultiVehicleWatchTask(m_multiVehicleTasks[t.first].get()))
                    {
                        auto multiWatchTask = std::static_pointer_cast<afrl::impact::MultiVehicleWatchTask>(m_multiVehicleTasks[t.first]);
                        int64_t N = multiWatchTask->getNumberVehicles();
                        BuildSummaryOptions(t.first, cleanResp, t.second, N);
                    }
                    else // somehow it is a multi-vehicle task but of unknown type
                    {
                        // just add all the summaries and call it good
                        auto tsum = new afrl::impact::TaskSummary;
                        tsum->setTaskID(t.first);
                        for (auto v : t.second)
                        {
                            tsum->getPerformingVehicles().push_back(v->clone());
                        }
                    }
                }
                else
                {
                    // just add all the summaries and call it good
                    auto tsum = new afrl::impact::TaskSummary;
                    tsum->setTaskID(t.first);
                    for (auto v : t.second)
                    {
                        tsum->getPerformingVehicles().push_back(v->clone());
                    }
                    cleanResp->getSummaries().push_back(tsum->clone());
                }
            }

            if (!cleanResp->getSummaries().empty())
            {
                // Finally re-constructed a full batch response, send along to global
                std::shared_ptr<avtas::lmcp::Object> pResponse = std::static_pointer_cast<avtas::lmcp::Object>(cleanResp);
                sendSharedLmcpObjectBroadcastMessage(pResponse);
                IMPACT_INFORM("sent batch summary id ", cleanResp->getResponseID());
            }

            // clear out this working response from the map
            m_workingResponse.erase(responseId);
            m_workingRequests.erase(responseId);
            return true;
        }

        void BatchSummaryService::BuildSummaryOptions(int64_t taskId, std::shared_ptr<afrl::impact::BatchSummaryResponse>& response,
            std::vector<std::shared_ptr<afrl::impact::VehicleSummary> >& vehicles, int64_t N)
        {
            auto scratchResponse = std::shared_ptr<afrl::impact::BatchSummaryResponse>(new afrl::impact::BatchSummaryResponse);
            // 100% completion is achieved by having N vehicles on task
            int64_t K = vehicles.size();
            int64_t startN = K - 1; // start with max number of vehicles
            if (startN >= N) // or max number of points
            { // if starting at n=0, then all combinations from 1 .. K
                startN = N - 1;
            }
            for (int64_t n = startN; n < N && n < K; n++)
            {
                auto tsum = new afrl::impact::TaskSummary;
                tsum->setTaskID(taskId);
                tsum->setBestEffort((n + 1.0) / N);
                std::vector<int> v(K);
                std::iota(v.begin(), v.end(), 0);
                for_each_permutation<std::vector<int>::iterator, f>(v.begin(), v.begin() + (n + 1), v.end(), f(tsum, vehicles, scratchResponse));
                delete tsum;
            }

            std::vector< std::tuple<int64_t, size_t, std::unordered_set<int64_t> > > combinations;
            for (size_t r = 0; r < scratchResponse->getSummaries().size(); r++)
            {
                std::unordered_set<int64_t> scratch;
                int64_t sumTime = 0;
                for (auto v : scratchResponse->getSummaries().at(r)->getPerformingVehicles())
                {
                    scratch.insert(v->getVehicleID());
                    sumTime += v->getTimeToArrive();
                }

                bool isInCombinations = false;
                for (auto c : combinations)
                {
                    bool isEquivalent = true;
                    for (auto e : scratch)
                    {
                        if (std::get<2>(c).find(e) == std::get<2>(c).end())
                        {
                            isEquivalent = false;
                            break;
                        }
                    }

                    if (isEquivalent)
                    {
                        isInCombinations = true;
                        // check update index/time
                        if (sumTime < std::get<0>(c))
                        {
                            std::get<0>(c) = sumTime;
                            std::get<1>(c) = r;
                        }
                        break;
                    }
                }

                if (!isInCombinations)
                {
                    combinations.push_back(std::make_tuple(sumTime, r, scratch));
                }
            }

            for (auto c : combinations)
            {
                response->getSummaries().push_back(scratchResponse->getSummaries().at(std::get<1>(c))->clone());
            }
        }

        void BatchSummaryService::HandleBatchSummaryRequest(std::shared_ptr<afrl::impact::BatchSummaryRequest> request)
        {

            //build TaskAutomationRequest messages

            int64_t responseId = m_responseId;
            m_responseId++;

            m_workingResponse[responseId].reset(new afrl::impact::BatchSummaryResponse);
            m_workingResponse[responseId]->setResponseID(request->getRequestID());

            m_workingRequests[responseId] = request;
            IMPACT_INFORM("received batch request ", request->getRequestID(), ". splitting into ", request->getTaskList().size() * request->getVehicles().size(), " internal task Automation Requests");

            for (auto task : request->getTaskList())
            {
                auto workingTaskSummary = new afrl::impact::TaskSummary();
                workingTaskSummary->setTaskID(task);
                m_workingResponse[responseId]->getSummaries().push_back(workingTaskSummary);

                for (auto vehicle : request->getVehicles())
                {
                    auto workingVehicleSummary = new afrl::impact::VehicleSummary();
                    workingVehicleSummary->setVehicleID(vehicle);
                    workingVehicleSummary->setDestinationTaskID(task);
                    workingVehicleSummary->setTimeToArrive(-1);
                    workingTaskSummary->getPerformingVehicles().push_back(workingVehicleSummary);
                }

                for (auto vehicle : request->getVehicles())
                {
                    auto taskAutomationRequest = std::make_shared<messages::task::TaskAutomationRequest>();
                    taskAutomationRequest->setSandBoxRequest(true);

                    taskAutomationRequest->setRequestID(m_taskAutomationRequestId); //need unique ID and a mapping to the batchsummary
                    m_batchSummaryRequestVsTaskAutomation[responseId].push_back(m_taskAutomationRequestId);
                    m_taskAutomationRequestId++;

                    //may have to add a processing algebra string here in the future.
                    auto automationRequest = std::make_shared<afrl::cmasi::AutomationRequest>();
                    automationRequest->getTaskList().push_back(task);
                    automationRequest->getEntityList().push_back(vehicle);

                    taskAutomationRequest->setOriginalRequest(automationRequest->clone());

                    //m_pendingTaskAutomationRequests[request->getRequestID()] = responseId;
                    std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(taskAutomationRequest);
                    m_pendingTaskAutomationRequests[taskAutomationRequest->getRequestID()] = taskAutomationRequest;
                    sendSharedLmcpObjectBroadcastMessage(pRequest);
                }

            }

        }

        void BatchSummaryService::UpdateSummaryUtil(afrl::impact::VehicleSummary * sum, std::vector<afrl::cmasi::Waypoint*> waypoints)
        {
            common::utilities::CUnitConversions unitConversions;

            //clone waypoints
            for (auto wp : waypoints)
            {
                sum->getWaypointList().push_back(wp->clone());
            }

            //set timeOnTask and timeToArrive
            afrl::cmasi::Waypoint* prev = nullptr;
            double timeOnTask = 0.0;
            double timeToArrive = 0.0;
            bool onTask = false;
            for (auto wp : waypoints)
            {
                if (!wp->getAssociatedTasks().empty())
                {
                    onTask = true;
                }
                if (prev)
                {
                    auto timeFromPrev = unitConversions.dGetLinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(prev->getLatitude(), prev->getLongitude(), wp->getLatitude(), wp->getLongitude()) / wp->getSpeed();
                    if (onTask)
                    {
                        timeOnTask += timeFromPrev;
                    }
                    else
                    {
                        timeToArrive += timeFromPrev;
                    }
                }
                prev = wp;
            }

            timeOnTask *= 1000;
            timeToArrive *= 1000;
            sum->setTimeOnTask(timeOnTask);
            sum->setTimeToArrive(timeToArrive);

            //set first waypoint
            if (sum->getWaypointList().size() > 0)
            {
                sum->setFirstWaypoint(sum->getWaypointList().front()->getNumber());
            }


        }


        void BatchSummaryService::UpdateSummary(afrl::impact::VehicleSummary* sum, std::vector<afrl::cmasi::Waypoint*> waypoints)
        {
            uxas::common::utilities::CUnitConversions unitConversions;


            double north, east;

            //check conflicts with ROZ. Assume individual waypoints came from planner and do not conflict. Attached actions might.
            for (auto wp : waypoints)
            {
                for (auto action : wp->getVehicleActionList())
                {
                    if (isLoiterAction(action))
                    {
                        afrl::cmasi::LoiterAction* loiter = dynamic_cast<afrl::cmasi::LoiterAction*>(action);
                        //GsPnt2 p;
                        unitConversions.ConvertLatLong_degToNorthEast_m(loiter->getLocation()->getLatitude(), loiter->getLocation()->getLongitude(), north, east);
                        auto length = loiter->getRadius();
                        //assume circular
                        //for (auto koz : m_keepOutZones)
                        //{
                        //    for (double rad = 0; rad < n_Const::c_Convert::dTwoPi(); rad += n_Const::c_Convert::dPiO10())
                        //    {
                        //        p.x = east + length * cos(rad);
                        //        p.y = north + length * sin(rad);
                        //        if (koz.second->contains(p))
                        //        {
                        //            sum->setConflictsWithROZ(true);
                        //            break;
                        //        }
                        //    }
                        //}
                    }
                }
            }

            // calculate 'EnergyRemaining'
            sum->setEnergyRemaining(100.0f);

            if (m_entityStates.find(sum->getVehicleID()) != m_entityStates.end())
            {
                // get current energy of vehicle and energy expenditure rate
                double e = m_entityStates[sum->getVehicleID()]->getEnergyAvailable(); // %
                double erate = m_entityStates[sum->getVehicleID()]->getActualEnergyRate(); // %/s

                int64_t time = sum->getTimeToArrive() + sum->getTimeOnTask();

                // linear approximation of energy remaining
                double eloss = time * erate / 1000.0; // time back to seconds from milliseconds
                e -= eloss;
                e = (e < 0) ? 0.0 : e;
                sum->setEnergyRemaining(e);
            }

            // check comm range
            bool inCommRange = false;
            for (auto t : m_towerLocations)
            {
                bool beyondThisTower = false;
                double tn, te;
                unitConversions.ConvertLatLong_degToNorthEast_m(t.second->getLatitude(), t.second->getLongitude(), tn, te);

                if (m_entityStates.find(sum->getVehicleID()) != m_entityStates.end() &&
                    m_towerRanges.find(t.first) != m_towerRanges.end())
                {
                    double vn, ve;
                    double towerRange = m_towerRanges[t.first].first;
                    if (!m_towerRanges[t.first].second)
                    {
                        towerRange = 1.0;
                    }

                    // set to max of vehicle, tower
                    if (m_entityConfigs.find(sum->getVehicleID()) != m_entityConfigs.end())
                    {
                        for (auto pay : m_entityConfigs[sum->getVehicleID()]->getPayloadConfigurationList())
                        {
                            if (afrl::impact::isRadioConfiguration(pay))
                            {
                                auto commpay = static_cast<afrl::impact::RadioConfiguration*>(pay);
                                if (commpay->getRange() > towerRange)
                                {
                                    towerRange = commpay->getRange();
                                }
                            }
                        }
                    }

                    unitConversions.ConvertLatLong_degToNorthEast_m(
                        m_entityStates[sum->getVehicleID()]->getLocation()->getLatitude(),
                        m_entityStates[sum->getVehicleID()]->getLocation()->getLongitude(), vn, ve);
                    double vdist = sqrt((tn - vn) * (tn - vn) + (te - ve) * (te - ve));
                    beyondThisTower = (vdist > towerRange);
                    for (auto wp : waypoints)
                    {
                        if (beyondThisTower)
                            break;
                        double pn, pe;
                        unitConversions.ConvertLatLong_degToNorthEast_m(wp->getLatitude(), wp->getLongitude(), pn, pe);
                        double pdist = sqrt((tn - pn) * (tn - pn) + (te - pe) * (te - pe));
                        for (auto a : wp->getVehicleActionList())
                        {
                            if (afrl::cmasi::isLoiterAction(a))
                            {
                                auto la = static_cast<afrl::cmasi::LoiterAction*>(a);
                                double wn, we;
                                unitConversions.ConvertLatLong_degToNorthEast_m(
                                    la->getLocation()->getLatitude(),
                                    la->getLocation()->getLongitude(), wn, we);
                                double wpdist = sqrt((wn - tn) * (wn - tn) + (we - te) * (we - te));
                                if ((la->getRadius() + wpdist) > pdist)
                                {
                                    // override distance if action is futher than waypoint
                                    pdist = la->getRadius() + wpdist;
                                }
                            }
                        }
                        beyondThisTower |= (pdist > towerRange);
                    }
                }
                if (!beyondThisTower)
                {
                    inCommRange = true;
                    break;
                }
            }

            sum->setBeyondCommRange(!inCommRange);
        }


        bool BatchSummaryService::LinearizeBoundary(afrl::cmasi::AbstractGeometry* boundary, VisiLibity::Polygon& poly)
        {
            uxas::common::utilities::CUnitConversions flatEarth;
            bool isValid = false;
            poly.clear();

            if (afrl::cmasi::isPolygon(boundary))
            {
                afrl::cmasi::Polygon* boundaryPolygon = (afrl::cmasi::Polygon*) boundary;
                for (unsigned int k = 0; k < boundaryPolygon->getBoundaryPoints().size(); k++)
                {
                    VisiLibity::Point pt;
                    double north, east;
                    flatEarth.ConvertLatLong_degToNorthEast_m(boundaryPolygon->getBoundaryPoints()[k]->getLatitude(), boundaryPolygon->getBoundaryPoints()[k]->getLongitude(), north, east);
                    pt.set_x(east);
                    pt.set_y(north);
                    poly.push_back(pt);
                }
                isValid = true;
            }
            else if (afrl::cmasi::isRectangle(boundary))
            {
                afrl::cmasi::Rectangle* rectangle = (afrl::cmasi::Rectangle*) boundary;
                VisiLibity::Point c;
                double north, east;
                flatEarth.ConvertLatLong_degToNorthEast_m(rectangle->getCenterPoint()->getLatitude(), rectangle->getCenterPoint()->getLongitude(), north, east);
                c.set_x(east);
                c.set_y(north);

                VisiLibity::Point pt;
                // note: north-aligned positive rotation is opposite direction of x-aligned positive rotation
                double a = -rectangle->getRotation() * n_Const::c_Convert::dDegreesToRadians();
                double w = rectangle->getWidth() / 2;
                double h = rectangle->getHeight() / 2;

                auto rot1 = VisiLibity::Point::rotate(VisiLibity::Point(east + w - c.x(), north + h - c.y()), a);
                rot1.set_x(rot1.x() + c.x());
                rot1.set_y(rot1.y() + c.y());

                auto rot2 = VisiLibity::Point::rotate(VisiLibity::Point(east - w - c.x(), north + h - c.y()), a);
                rot2.set_x(rot2.x() + c.x());
                rot2.set_y(rot2.y() + c.y());

                auto rot3 = VisiLibity::Point::rotate(VisiLibity::Point(east - w - c.x(), north - h - c.y()), a);
                rot3.set_x(rot3.x() + c.x());
                rot3.set_y(rot3.y() + c.y());

                auto rot4 = VisiLibity::Point::rotate(VisiLibity::Point(east + w - c.x(), north - h - c.y()), a);
                rot4.set_x(rot4.x() + c.x());
                rot4.set_y(rot4.y() + c.y());

                poly.push_back(rot1);
                poly.push_back(rot2);
                poly.push_back(rot3);
                poly.push_back(rot4);

                isValid = true;
            }
            else if (afrl::cmasi::isCircle(boundary))
            {
                afrl::cmasi::Circle* circle = (afrl::cmasi::Circle*) boundary;
                VisiLibity::Point c;
                double north, east;
                flatEarth.ConvertLatLong_degToNorthEast_m(circle->getCenterPoint()->getLatitude(), circle->getCenterPoint()->getLongitude(), north, east);
                c.set_x(east);
                c.set_y(north);
                double r = circle->getRadius() / cos(10.0 * n_Const::c_Convert::dDegreesToRadians());

                for (uint32_t k = 0; k < 18; k++)
                {
                    VisiLibity::Point pt;
                    pt.set_x(c.x() + r * cos(n_Const::c_Convert::dTwoPi() * k / 18.0));
                    pt.set_y(c.y() + r * sin(n_Const::c_Convert::dTwoPi() * k / 18.0));
                    poly.push_back(pt);
                }

                isValid = true;
            }

            return isValid;
        }


        std::shared_ptr<GsPolygon> BatchSummaryService::FromAbstractGeometry(afrl::cmasi::AbstractGeometry *geom)
        {
            VisiLibity::Polygon poly;
            LinearizeBoundary(geom, poly);
            poly.eliminate_redundant_vertices(1.0);
            if (poly.area() < 0)
            {
                poly.reverse();
            }
            auto ret = std::make_shared<GsPolygon>();
            for (int i = 0; i < poly.n(); i++)
            {
                ret->push().set((float)poly[i].x(), (float)poly[i].y());
            }
            return ret;
        }
    }; //namespace service
}; //namespace uxas

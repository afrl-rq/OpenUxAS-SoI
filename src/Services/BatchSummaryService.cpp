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
#define STRING_XML_FAST_PLAN "FastPlan"
#define STRING_XML_LANE_SPACING "LaneSpacing"


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

bool BatchSummaryService::initialize()
{

    return true;
}

bool
    BatchSummaryService::configure(const pugi::xml_node & ndComponent)

{
    std::string strFastPlan = ndComponent.attribute(STRING_XML_FAST_PLAN).value();
    if (!strFastPlan.empty())
    {
        m_fastPlan = ndComponent.attribute(STRING_XML_FAST_PLAN).as_bool();
    }


    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    for (auto descendant : afrl::cmasi::EntityStateDescendants())
        addSubscriptionAddress(descendant);
    
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    for (auto descendant : afrl::cmasi::EntityConfigurationDescendants())
        addSubscriptionAddress(descendant);


    //assume all KOZs apply to all vehicles for checking conflictsWithROZ
    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);

    // Primary messages for actual route construction
    addSubscriptionAddress(afrl::impact::BatchSummaryRequest::Subscription);
    addSubscriptionAddress(messages::task::TaskAutomationResponse::Subscription);

    return true; // may not have the proper fast plan value, but proceed anyway
}

bool BatchSummaryService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    if (afrl::impact::isBatchSummaryRequest(receivedLmcpMessage->m_object.get()))
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
    else if (std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object))
    {
        auto state = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        int64_t id = state->getID();
        m_entityStates[id] = state;

   if (afrl::impact::isRadioTowerState(receivedLmcpMessage->m_object.get()))
   {
       m_towerLocations[id] = std::shared_ptr<afrl::cmasi::Location3D>(state->getLocation()->clone());
       auto rs = std::static_pointer_cast<afrl::impact::RadioTowerState>(receivedLmcpMessage->m_object);
       if (m_towerRanges.find(id) != m_towerRanges.end())
       {
           m_towerRanges[id].second = rs->getEnabled();
       }
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

void BatchSummaryService::HandleTaskAutomationResponse(const std::shared_ptr<messages::task::TaskAutomationResponse>& taskAutomationResponse)
{

    //auto taskAutomationRequest = m_pendingTaskAutomationRequests.find(taskAutomationResponse->getResponseID())->second;
    m_pendingTaskAutomationRequests.erase(taskAutomationResponse->getResponseID());

    //remove pending task automation response. If any are empty, finalize
    std::list<int64_t> finishedIds;
    auto batchSummary = std::find_if(m_batchSummaryRequestVsTaskAutomation.begin(), m_batchSummaryRequestVsTaskAutomation.end(),
        [&](const std::pair<int64_t, std::list<int64_t>> x)
    {return std::find(x.second.begin(), x.second.end(), taskAutomationResponse->getResponseID()) != x.second.end(); });

    if (batchSummary != m_batchSummaryRequestVsTaskAutomation.end())
    {
        auto batchSummaryResponse = m_workingResponse.find((*batchSummary).first);
        
        if (batchSummaryResponse != m_workingResponse.end())
        {
            UpdateTaskSummariesUtil(batchSummaryResponse->second->getSummaries(), taskAutomationResponse->getOriginalResponse()->getMissionCommandList());
            
            //iterate through vehicle summaries to set conflicts with ROZ and beyondCommRange
            for (auto taskSummary : batchSummaryResponse->second->getSummaries())
            {
                for (auto vehicleSummary : taskSummary->getPerformingVehicles())
                {
                    BatchSummaryService::UpdateVehicleSummary(vehicleSummary);
                }
            }
        }

        (*batchSummary).second.remove(taskAutomationResponse->getResponseID());
        if ((*batchSummary).second.empty())
        {
            finishedIds.push_back((*batchSummary).first);
        }

    }


    for (auto finishedId : finishedIds)
    {
        FinalizeBatchRequest(finishedId);
        m_batchSummaryRequestVsTaskAutomation.erase(finishedId);
    }
}

bool BatchSummaryService::FinalizeBatchRequest(int64_t responseId)
{
    // this function is only called when the summaries have been composed
    // only need to check for possible 'best efforts' regarding the tasks in the
    // current summary list

    if (m_workingResponse.find(responseId) == m_workingResponse.end())
        return false;
    auto resp = m_workingResponse[responseId];

    // Finally re-constructed a full batch response, send along to global
    sendSharedLmcpObjectBroadcastMessage(resp);
    IMPACT_INFORM("sent batch summary id ", resp->getResponseID());

    // clear out this working response from the map
    m_workingResponse.erase(responseId);
    m_workingRequests.erase(responseId);
    return true;
}


void BatchSummaryService::HandleBatchSummaryRequest(std::shared_ptr<afrl::impact::BatchSummaryRequest> request)
{

    //build TaskAutomationRequest messages

    int64_t responseId = m_responseId;
    m_responseId++;

    m_workingResponse[responseId].reset(new afrl::impact::BatchSummaryResponse);
    m_workingResponse[responseId]->setResponseID(request->getRequestID());

    m_workingRequests[responseId] = request;

    //go ahead and make TaskSummaries
    for (auto task : request->getTaskList())
    {
        auto workingSummary = std::make_shared<afrl::impact::TaskSummary>();
        workingSummary->setTaskID(task);
        workingSummary->setBestEffort(100);
        m_workingResponse[responseId]->getSummaries().push_back(workingSummary->clone());
    }

    std::vector<std::shared_ptr<afrl::cmasi::AutomationRequest>> requests;
    if (request->getTaskRelationships().empty()) //no relationship. create a request per each vehicle task pair
    {
        for (auto task : request->getTaskList())
        {
            auto workingTaskSummary = std::find_if(m_workingResponse[responseId]->getSummaries().begin(), m_workingResponse[responseId]->getSummaries().end(), [&](const afrl::impact::TaskSummary* x) { return x->getTaskID() == task; });

            for (auto vehicle : request->getVehicles())
            {
                auto automationRequest = std::make_shared<afrl::cmasi::AutomationRequest>();
                automationRequest->getTaskList().push_back(task);
                automationRequest->getEntityList().push_back(vehicle);
                requests.push_back(automationRequest);

                auto summary = std::make_shared<afrl::impact::VehicleSummary>();
                summary->setVehicleID(vehicle);
                summary->setDestinationTaskID(task);
                summary->setTimeOnTask(-1);
                summary->setTimeToArrive(-1);
                if (workingTaskSummary != m_workingResponse[responseId]->getSummaries().end())
                {
                    (*workingTaskSummary)->getPerformingVehicles().push_back(summary->clone());
                }
            }
        }
    }
    else //assume realtionship wants intertask information. Split accordingly
    {
        for (auto vehicle : request->getVehicles())
        {
            for (auto taski : request->getTaskList())
            {
                //vehicle to task summary
                auto workingTaskSummaryi = std::find_if(m_workingResponse[responseId]->getSummaries().begin(), m_workingResponse[responseId]->getSummaries().end(), [&](const afrl::impact::TaskSummary* x) { return x->getTaskID() == taski; });
                auto summaryVehicleToTask = std::make_shared<afrl::impact::VehicleSummary>();
                summaryVehicleToTask->setVehicleID(vehicle);
                summaryVehicleToTask->setDestinationTaskID(taski);
                summaryVehicleToTask->setTimeOnTask(-1);
                summaryVehicleToTask->setTimeToArrive(-1);

                if (workingTaskSummaryi != m_workingResponse[responseId]->getSummaries().end())
                {
                    (*workingTaskSummaryi)->getPerformingVehicles().push_back(summaryVehicleToTask->clone());
                }

                for (auto taskj : request ->getTaskList())
                {
                    if (taski == taskj)
                    {
                        continue;
                    }
                    auto automationRequest = std::make_shared<afrl::cmasi::AutomationRequest>();

                    automationRequest->getTaskList().push_back(taski);
                    automationRequest->getTaskList().push_back(taskj);
                    automationRequest->setTaskRelationships(".(p" + std::to_string(taski) + " p" + std::to_string(taskj) + ")");
                    automationRequest->getEntityList().push_back(vehicle);

                    //task to task summaries
                    auto workingTaskSummaryj = std::find_if(m_workingResponse[responseId]->getSummaries().begin(), m_workingResponse[responseId]->getSummaries().end(), [&](const afrl::impact::TaskSummary* x) { return x->getTaskID() == taskj; });
                    auto summaryTaskToTask = std::make_shared<afrl::impact::VehicleSummary>();
                    summaryTaskToTask->setVehicleID(vehicle);
                    summaryTaskToTask->setInitialTaskID(taski);
                    summaryTaskToTask->setDestinationTaskID(taskj);
                    summaryTaskToTask->setTimeOnTask(-1);
                    summaryTaskToTask->setTimeToArrive(-1);


                    if (workingTaskSummaryj != m_workingResponse[responseId]->getSummaries().end())
                    {
                        (*workingTaskSummaryj)->getPerformingVehicles().push_back(summaryTaskToTask->clone());
                    }


                    requests.push_back(automationRequest);
                }

            }

        }
    }



    //wrap requests up to send into TaskAutomationRequests
    for (auto requestToSend : requests)
    {
        auto taskAutomationRequest = std::make_shared<messages::task::TaskAutomationRequest>();
        taskAutomationRequest->setSandBoxRequest(true);
        taskAutomationRequest->setRequestID(m_taskAutomationRequestId);
        m_taskAutomationRequestId++;
        taskAutomationRequest->setOriginalRequest(requestToSend->clone());

        std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(taskAutomationRequest);
        m_pendingTaskAutomationRequests[taskAutomationRequest->getRequestID()] = taskAutomationRequest;
        m_batchSummaryRequestVsTaskAutomation[responseId].push_back(taskAutomationRequest->getRequestID());
        sendSharedLmcpObjectBroadcastMessage(pRequest);
    }
    IMPACT_INFORM("received batch request ", request->getRequestID(), ". split into ", requests.size(), " internal task Automation Requests");
    if (requests.empty())
    {
        FinalizeBatchRequest(responseId);
    }
}

void BatchSummaryService::UpdateSummaryUtil(afrl::impact::VehicleSummary * sum, const std::vector<afrl::cmasi::Waypoint*>::iterator& task_begin, const std::vector<afrl::cmasi::Waypoint*>::iterator& task_end)
{
    if (task_begin == task_end)
    {
        return;
    }

    uxas::common::utilities::CUnitConversions unitConversions;

    //clone waypoints
    for (auto wp = task_begin; wp != task_end; wp++)
    {
        sum->getWaypointList().push_back((*wp)->clone());
    }

    //set timeOnTask and timeToArrive
    afrl::cmasi::Waypoint* prev = nullptr;
    double timeOnTask = 0.0;
    double timeToArrive = 0.0;
    bool onTask;
    for (auto wp = task_begin; wp != task_end; wp++)
    {
      if (prev)
      {
        onTask = !prev->getAssociatedTasks().empty();

        auto timeFromPrev = unitConversions.dGetLinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(prev->getLatitude(), prev->getLongitude(), (*wp)->getLatitude(), (*wp)->getLongitude()) / (*wp)->getSpeed();
        if (onTask)
        {
          timeOnTask += timeFromPrev;
        }
        else
        {
          timeToArrive += timeFromPrev;
        }
      }
        prev = *wp;
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

void BatchSummaryService::UpdateTaskSummariesUtil(std::vector<afrl::impact::TaskSummary*> taskSummaries, std::vector<afrl::cmasi::MissionCommand*> missions)
{
    //iterate through waypoints to reconstruct tasks.
    //this gives ordering and lists of waypoints to reconstruct costs.
    for (auto missionCommand : missions)
    {
        auto vehicle = missionCommand->getVehicleID();
        auto taskStart = missionCommand->getWaypointList().begin();
        bool iteratingToTask = true;
        auto workingTask = 0;
        auto prevTask = 0;
        for (auto wpIter = missionCommand->getWaypointList().begin(); wpIter != missionCommand->getWaypointList().end(); wpIter++)
        {
            if (!(*wpIter)->getAssociatedTasks().empty() && *wpIter != missionCommand->getWaypointList().back())
            {
                if (iteratingToTask) //found first waypoint on task
                {
                    iteratingToTask = false;
                    prevTask = workingTask;
                    workingTask = (*wpIter)->getAssociatedTasks().front();
                }
            }
            else
            {
                if (!iteratingToTask) //found last waypoint
                {
                    iteratingToTask = true;
                    auto taskEnd = wpIter;
                    //get the right TaskSummary
                    auto workingTaskSummary = std::find_if(taskSummaries.begin(), taskSummaries.end(), [&](const afrl::impact::TaskSummary* x) { return x->getTaskID() == workingTask; });
                    if (workingTaskSummary != taskSummaries.end())
                    {
                        //get the right vehicleSummary
                        auto vehicleSummary = std::find_if((*workingTaskSummary)->getPerformingVehicles().begin(), (*workingTaskSummary)->getPerformingVehicles().end(), 
                            [&](const afrl::impact::VehicleSummary* x) {return x->getVehicleID() == vehicle && x->getDestinationTaskID() == workingTask && x->getInitialTaskID() == prevTask; });
                        if (vehicleSummary != (*workingTaskSummary)->getPerformingVehicles().end())
                        {
                            UpdateSummaryUtil(*vehicleSummary, taskStart, taskEnd + 1);
                            (*vehicleSummary)->setInitialTaskID(prevTask);
                        }
                    }
                    //set next taskStart
                    taskStart = wpIter;
                }
            }
        }
    }
}


void BatchSummaryService::UpdateVehicleSummary(afrl::impact::VehicleSummary * vehicleSum)
{
    uxas::common::utilities::CUnitConversions unitConversions;


    double north, east;
    //check conflicts with ROZ. Assume individual waypoints came from planner and do not conflict. Attached actions might.
    for (auto wp : vehicleSum->getWaypointList())
    {
        for (auto action : wp->getVehicleActionList())
        {
            if (afrl::cmasi::isLoiterAction(action))
            {
                afrl::cmasi::LoiterAction* loiter = dynamic_cast<afrl::cmasi::LoiterAction*>(action);
                VisiLibity::Point p;
                unitConversions.ConvertLatLong_degToNorthEast_m(loiter->getLocation()->getLatitude(), loiter->getLocation()->getLongitude(), north, east);
                auto length = loiter->getRadius();
                //assume circular
                for (auto koz : m_keepOutZones)
                {
                    for (double rad = 0; rad < n_Const::c_Convert::dTwoPi(); rad += n_Const::c_Convert::dPiO10())
                    {
                        p.set_x(east + length * cos(rad));
                        p.set_y(north + length * sin(rad));
                        if (p.in(*koz.second, 1e-4))
                        {
                            vehicleSum->setConflictsWithROZ(true);
                            break;
                        }
                    }
                }
            }
        }
    }

    // calculate 'EnergyRemaining'
    vehicleSum->setEnergyRemaining(100.0f);

    if (m_entityStates.find(vehicleSum->getVehicleID()) != m_entityStates.end())
    {
        // get current energy of vehicle and energy expenditure rate
        double e = m_entityStates[vehicleSum->getVehicleID()]->getEnergyAvailable(); // %
        double erate = m_entityStates[vehicleSum->getVehicleID()]->getActualEnergyRate(); // %/s

        int64_t time = vehicleSum->getTimeToArrive() + vehicleSum->getTimeOnTask();

        // linear approximation of energy remaining
        double eloss = time * erate / 1000.0; // time back to seconds from milliseconds
        e -= eloss;
        e = (e < 0) ? 0.0 : e;
        vehicleSum->setEnergyRemaining(e);
    }

    // check comm range
    bool inCommRange = false;
    for (auto t : m_towerLocations)
    {
        bool beyondThisTower = false;
        double tn, te;
        unitConversions.ConvertLatLong_degToNorthEast_m(t.second->getLatitude(), t.second->getLongitude(), tn, te);

        if (m_entityStates.find(vehicleSum->getVehicleID()) != m_entityStates.end() &&
            m_towerRanges.find(t.first) != m_towerRanges.end())
        {
            double vn, ve;
            double towerRange = m_towerRanges[t.first].first;
            if (!m_towerRanges[t.first].second)
            {
                towerRange = 1.0;
            }

            // set to max of vehicle, tower
            if (m_entityConfigs.find(vehicleSum->getVehicleID()) != m_entityConfigs.end())
            {
                for (auto pay : m_entityConfigs[vehicleSum->getVehicleID()]->getPayloadConfigurationList())
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
                m_entityStates[vehicleSum->getVehicleID()]->getLocation()->getLatitude(),
                m_entityStates[vehicleSum->getVehicleID()]->getLocation()->getLongitude(), vn, ve);
            double vdist = sqrt((tn - vn) * (tn - vn) + (te - ve) * (te - ve));
            beyondThisTower = (vdist > towerRange);
            for (auto wp : vehicleSum->getWaypointList())
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

    vehicleSum->setBeyondCommRange(!inCommRange);
}


bool BatchSummaryService::LinearizeBoundary(afrl::cmasi::AbstractGeometry* boundary, std::shared_ptr<VisiLibity::Polygon>& poly)
{
    uxas::common::utilities::CUnitConversions flatEarth;
    bool isValid = false;
    poly->clear();

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
            poly->push_back(pt);
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

        poly->push_back(VisiLibity::Point::rotate(VisiLibity::Point(east + w, north + h) - c, a) + c);
        poly->push_back(VisiLibity::Point::rotate(VisiLibity::Point(east - w, north + h) - c, a) + c);
        poly->push_back(VisiLibity::Point::rotate(VisiLibity::Point(east - w, north - h) - c, a) + c);
        poly->push_back(VisiLibity::Point::rotate(VisiLibity::Point(east + w, north - h) - c, a) + c);

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
            poly->push_back(pt);
        }

        isValid = true;
    }

    return isValid;
}


std::shared_ptr<VisiLibity::Polygon> BatchSummaryService::FromAbstractGeometry(afrl::cmasi::AbstractGeometry *geom)
{
    auto poly = std::shared_ptr<VisiLibity::Polygon>(new VisiLibity::Polygon);
    LinearizeBoundary(geom, poly);
    poly->eliminate_redundant_vertices(1.0);
    if (poly->area() < 0)
    {
        poly->reverse();
    }
    
    return poly;
}
}; //namespace service
}; //namespace uxas

void ras_configure()
{
  std::string strBasePath = m_workDirectoryPath;
  uint32_t ui32EntityID = m_entityId;
  uint32_t ui32LmcpMessageSize_max = 100000;
  std::stringstream sstrErrors;
  
  std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();
  
  if (!ndComponent.attribute(STRING_XML_FAST_PLAN).empty())
  {
      // Only supported parameter: disables local route planner for
      // computationally expensive ground route calculations
      m_fastPlan = ndComponent.attribute(STRING_XML_FAST_PLAN).as_bool();
  }

  __COPPER_HANDSHAKE__("configure");

  // track states and configurations for assignment cost matrix calculation
  // [EntityStates] are used to calculate costs from current position to first task
  // [EntityConfigurations] are used for nominal speed values (all costs are in terms of time to arrive)
  addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
  addSubscriptionAddress(afrl::impact::GroundVehicleState::Subscription);
  addSubscriptionAddress(afrl::impact::SurfaceVehicleState::Subscription);
  addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
  addSubscriptionAddress(afrl::impact::GroundVehicleConfiguration::Subscription);
  addSubscriptionAddress(afrl::impact::SurfaceVehicleConfiguration::Subscription);
  
  // track requests to kickoff matrix calculation
  addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
  
  // subscribe to task plan options to build matrix
  addSubscriptionAddress(uxas::messages::task::TaskPlanOptions::Subscription);
  
  // handle batch route requests
  addSubscriptionAddress(uxas::messages::route::RouteRequest::Subscription);
  
  // listen for responses to requests from route planner(s)
  addSubscriptionAddress(uxas::messages::route::RoutePlanResponse::Subscription);
  
  // Subscribe to group messages (whisper from local route planner)
  //TODO REVIEW DESIGN "RouteAggregator" "RoutePlanner" flip message addressing effecting session behavior
  //return true; // may not have the proper fast plan value, but proceed anyway
}

struct LmcpMessage
{
    int m_object;
};

void ras_processReceivedLmcpMessage(struct LmcpMessage *receivedLmcpMessage)
{
  __COPPER_HANDSHAKE__("process");
  // successful de-serialization of message
  if (uxas_messages_route_isRoutePlanResponse(receivedLmcpMessage->m_object))
  {
      auto rplan = std_static_pointer_cast<uxas_messages_route_RoutePlanResponse>(receivedLmcpMessage->m_object);
      __COPPER_HANDSHAKE__("route_plan_response");
      m_routePlanResponses[rplan->getResponseID()] = rplan;
      for (auto p : rplan->getRouteResponses())
      {
          m_routePlans[p->getRouteID()] = std_make_pair(rplan->getResponseID(), std_shared_ptr<uxas_messages_route_RoutePlan>(p->clone()));
      }
      ras_CheckAllRoutePlans();
  }
  else if (uxas_messages_route_isRouteRequest(receivedLmcpMessage->m_object))
  {
      __COPPER_HANDSHAKE__("route_request");
      //auto rreq = std_static_pointer_cast<uxas_messages_route_RouteRequest>(receivedLmcpMessage->m_object);
      ras_HandleRouteRequest(rreq);
  }
  else if (afrl_cmasi_isAirVehicleState(receivedLmcpMessage->m_object))
  {
      int64_t id = std_static_pointer_cast<afrl_cmasi_EntityState>(receivedLmcpMessage->m_object)->getID();
      __COPPER_HANDSHAKE__("air_vehicle_state");
      m_entityStates[id] = std_static_pointer_cast<afrl_cmasi_EntityState>(receivedLmcpMessage->m_object);
      m_airVehicles.insert(id);
  }
  else if (afrl_impact_isGroundVehicleState(receivedLmcpMessage->m_object))
  {
      int64_t id = std_static_pointer_cast<afrl_cmasi_EntityState>(receivedLmcpMessage->m_object)->getID();
      __COPPER_HANDSHAKE__("ground_vehicle_state");
      m_entityStates[id] = std_static_pointer_cast<afrl_cmasi_EntityState>(receivedLmcpMessage->m_object);
      m_groundVehicles.insert(id);
  }
  else if (afrl_impact_isSurfaceVehicleState(receivedLmcpMessage->m_object))
  {
      int64_t id = std_static_pointer_cast<afrl_cmasi_EntityState>(receivedLmcpMessage->m_object)->getID();
      __COPPER_HANDSHAKE__("surface_vehicle_state");
      m_entityStates[id] = std_static_pointer_cast<afrl_cmasi_EntityState>(receivedLmcpMessage->m_object);
      m_surfaceVehicles.insert(id);
  }
  else if (afrl_cmasi_isAirVehicleConfiguration(receivedLmcpMessage->m_object))
  {
      int64_t id = std_static_pointer_cast<afrl_cmasi_EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
      __COPPER_HANDSHAKE__("air_vehicle_configuration");
      m_entityConfigurations[id] = std_static_pointer_cast<afrl_cmasi_EntityConfiguration>(receivedLmcpMessage->m_object);
      m_airVehicles.insert(id);
  }
  else if (afrl_impact_isGroundVehicleConfiguration(receivedLmcpMessage->m_object))
  {
      int64_t id = std_static_pointer_cast<afrl_cmasi_EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
      __COPPER_HANDSHAKE__("ground_vehicle_configuration");
      m_entityConfigurations[id] = std_static_pointer_cast<afrl_cmasi_EntityConfiguration>(receivedLmcpMessage->m_object);
      m_groundVehicles.insert(id);
  }
  else if (afrl_impact_isSurfaceVehicleConfiguration(receivedLmcpMessage->m_object))
  {
      int64_t id = std_static_pointer_cast<afrl_cmasi_EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
      __COPPER_HANDSHAKE__("surface_vehicle_configuration");
      m_entityConfigurations[id] = std_static_pointer_cast<afrl_cmasi_EntityConfiguration>(receivedLmcpMessage->m_object);
      m_surfaceVehicles.insert(id);
  }
  else if (uxas_messages_task_isUniqueAutomationRequest(receivedLmcpMessage->m_object))
  {
      auto areq = std_static_pointer_cast<uxas_messages_task_UniqueAutomationRequest>(receivedLmcpMessage->m_object);
      __COPPER_HANDSHAKE__("unique_automation_request");
      m_uniqueAutomationRequests[m_autoRequestId++] = areq;
      //ResetTaskOptions(areq); // clear m_taskOptions and wait for refresh from tasks
      ras_CheckAllTaskOptionsReceived();
  }
  else if (afrl_impact_isImpactAutomationRequest(receivedLmcpMessage->m_object))
  {
      auto sreq = std_static_pointer_cast<afrl_impact_ImpactAutomationRequest>(receivedLmcpMessage->m_object);
      auto areq = std_shared_ptr<uxas_messages_task_UniqueAutomationRequest>();
      __COPPER_HANDSHAKE__("impact_automation_request");
      areq->setOriginalRequest(sreq->getTrialRequest()->clone());
      m_uniqueAutomationRequests[m_autoRequestId++] = areq;
      areq->setRequestID(m_autoRequestId);
      //ResetTaskOptions(areq); // clear m_taskOptions and wait for refresh from tasks
      ras_CheckAllTaskOptionsReceived();
  }
  else if (uxas_messages_task_isTaskPlanOptions(receivedLmcpMessage->m_object))
  {
      auto taskOptions = std_static_pointer_cast<uxas_messages_task_TaskPlanOptions>(receivedLmcpMessage->m_object);
      __COPPER_HANDSHAKE__("task_plan_options");
      m_taskOptions[taskOptions->getTaskID()] = taskOptions;
      ras_CheckAllTaskOptionsReceived();
  }
  //return (false); // always false implies never terminating service from here
}

void ras_CheckAllTaskOptionsReceived()
{
    // loop through all automation requests; delete when fulfilled
    auto areqIter = m_uniqueAutomationRequests.begin();
    while (areqIter != m_uniqueAutomationRequests.end())
    {
        // check that to see if all options from all tasks have been received for this request
        bool isAllReceived{true};
        for (size_t t = 0; t < areqIter->second->getOriginalRequest()->getTaskList().size(); t++)
        {
            int64_t taskId = areqIter->second->getOriginalRequest()->getTaskList().at(t);
            if (m_taskOptions.find(taskId) == m_taskOptions.end())
            {
                isAllReceived = false;
                break;
            }
        }

        // if all task options have NOT been received, wait until more come
        if (isAllReceived)
        {
            // Build messages for matrix
            BuildMatrixRequests(areqIter->first, areqIter->second);
        }
        areqIter++;
    }
}

void ras_HandleRouteRequest(int request)
{
    if (request->getVehicleID().empty())
    {
        request->getVehicleID().reserve(m_entityStates.size());
        for (const auto& v : m_entityStates)
        {
            request->getVehicleID().push_back(v.second->getID());
        }
    }

    for (const int64_t& vehicleId : request->getVehicleID())
    {
        // create a new route plan request
        std::shared_ptr<uxas::messages::route::RoutePlanRequest> planRequest(new uxas::messages::route::RoutePlanRequest);
        std::shared_ptr<avtas::lmcp::Object> pRequest;
        planRequest->setAssociatedTaskID(request->getAssociatedTaskID());
        planRequest->setIsCostOnlyRequest(request->getIsCostOnlyRequest());
        planRequest->setOperatingRegion(request->getOperatingRegion());
        planRequest->setVehicleID(vehicleId);
        planRequest->setRequestID(m_routeRequestId);

        m_pendingRoute[request->getRequestID()].insert(m_routeRequestId);
        m_routeRequestId++;

        for (auto& r : request->getRouteRequests())
        {
            planRequest->getRouteRequests().push_back(r->clone());
        }


        pRequest = std::static_pointer_cast<avtas::lmcp::Object>(planRequest);
        if (m_groundVehicles.find(vehicleId) != m_groundVehicles.end())
        {
            if (m_fastPlan)
            {
                // short-circuit and just plan with straight line planner
                EuclideanPlan(planRequest);
            }
            else
            {
                // send externally
                sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::GroundPathPlanner(), pRequest);
                __COPPER_HANDSHAKE__("route_plan_request");
            }
        }
        else
        {
            // send to aircraft planner
            sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::AircraftPathPlanner(), pRequest);
            __COPPER_HANDSHAKE__("route_plan_request");
        }
    }

    // if fast planning, then all routes should be complete; kick off response
    if (m_fastPlan)
    {
        ras_CheckAllRoutePlans();
    }
}

void ras_CheckAllRoutePlans()
{
    int k = 0;
    
    // check pending route requests
    int i = m_pendingRoute.begin();
    while (i != m_pendingRoute.end())
    {
        bool isFulfilled = true;
        for (const int64_t& j : i->second)
        {
            if (m_routePlanResponses.find(j) == m_routePlanResponses.end())
            {
                isFulfilled = false;
                break;
            }
        }

        if (isFulfilled)
        {
            ras_SendRouteResponse(i->first);
            i = m_pendingRoute.erase(i);
        }
        else
        {
            i++;
        }
    }

    // check pending automation requests
    k = m_pendingAutoReq.begin();
    while (k != m_pendingAutoReq.end())
    {
        bool isFulfilled = true;
        for (const int64_t& j : k->second)
        {
            if (m_routePlans.find(j) == m_routePlans.end())
            {
                isFulfilled = false;
                break;
            }
        }

        if (isFulfilled)
        {
            SendMatrix(k->first);
            // finished with this automation request, discard
            m_uniqueAutomationRequests.erase(k->first);
            k = m_pendingAutoReq.erase(k);
        }
        else
        {
            k++;
        }
    }
}

void ras_SendRouteResponse(int64_t routeKey)
{
    std::shared_ptr<avtas::lmcp::Object> pResponse;
    auto response = std::shared_ptr<uxas::messages::route::RouteResponse>(new uxas::messages::route::RouteResponse);
    response->setResponseID(routeKey);
    response->getRoutes().reserve(m_pendingRoute[routeKey].size());
    for (auto& rId : m_pendingRoute[routeKey])
    {
        auto plan = m_routePlanResponses.find(rId);
        if (plan != m_routePlanResponses.end())
        {
            response->getRoutes().push_back(plan->second->clone());

            // delete all individual routes from storage
            for (auto& i : plan->second->getRouteResponses())
            {
                m_routePlans.erase(i->getRouteID());
            }
            m_routePlanResponses.erase(plan);
        }
    }

    // send the results of the query
    pResponse = std::static_pointer_cast<avtas::lmcp::Object>(response);
    sendSharedLmcpObjectBroadcastMessage(pResponse);
    __COPPER_HANDSHAKE__("route_response");
}

void ras_service()
{
    struct LmcpMessage msg;
    ras_configure();
    while(1)
        ras_processReceivedLmcpMessage(&msg);
}


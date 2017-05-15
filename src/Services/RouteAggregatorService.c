void ras_configure()
{
  __COPPER_HANDSHAKE__("configure");

  /*
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
  */
  
  // track states and configurations for assignment cost matrix calculation
  // [EntityStates] are used to calculate costs from current position to first task
  // [EntityConfigurations] are used for nominal speed values (all costs are in terms of time to arrive)
  __COPPER_HANDSHAKE__("sub_afrl::cmasi::AirVehicleState::Subscription");
  __COPPER_HANDSHAKE__("sub_afrl::impact::GroundVehicleState::Subscription");
  __COPPER_HANDSHAKE__("sub_afrl::impact::SurfaceVehicleState::Subscription");
  __COPPER_HANDSHAKE__("sub_afrl::cmasi::AirVehicleConfiguration::Subscription");
  __COPPER_HANDSHAKE__("sub_afrl::impact::GroundVehicleConfiguration::Subscription");
  __COPPER_HANDSHAKE__("sub_afrl::impact::SurfaceVehicleConfiguration::Subscription");

  // track requests to kickoff matrix calculation
  __COPPER_HANDSHAKE__("sub_uxas::messages::task::UniqueAutomationRequest::Subscription");
  
  // subscribe to task plan options to build matrix
  __COPPER_HANDSHAKE__("sub_uxas::messages::task::TaskPlanOptions::Subscription");
  
  // handle batch route requests
  __COPPER_HANDSHAKE__("sub_uxas::messages::route::RouteRequest::Subscription");

  // listen for responses to requests from route planner(s)
  __COPPER_HANDSHAKE__("sub_uxas::messages::route::RoutePlanResponse::Subscription");
  
  // Subscribe to group messages (whisper from local route planner)
  //TODO REVIEW DESIGN "RouteAggregator" "RoutePlanner" flip message addressing effecting session behavior
  //return true; // may not have the proper fast plan value, but proceed anyway
}

void ras_processReceivedLmcpMessage()
{
  __COPPER_HANDSHAKE__("process");
}

void ras_service()
{
  ras_configure();
  for(;;) ras_processReceivedLmcpMessage();
}


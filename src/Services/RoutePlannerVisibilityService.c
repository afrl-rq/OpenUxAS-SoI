void rpvs_configure()
{
    bool isSucceeded{true};
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();
    //assert(strComponentType==STRING_XML_COMPONENT_TYPE)
    __COPPER_HANDSHAKE__("configure");

    if (!ndComponent.attribute(STRING_XML_TURN_RADIUS_OFFSET_M).empty())
    {
        m_turnRadiusOffset_m = ndComponent.attribute(STRING_XML_TURN_RADIUS_OFFSET_M).as_double();
    }

    if (!ndComponent.attribute(STRING_XML_IS_ROUTE_AGGREGATOR).empty())
    {
        m_isRoutAggregator = ndComponent.attribute(STRING_XML_IS_ROUTE_AGGREGATOR).as_bool();
    }

    if (!ndComponent.attribute(STRING_XML_OSM_FILE_NAME).empty())
    {
        std::string osmFileName = ndComponent.attribute(STRING_XML_OSM_FILE_NAME).value();
        auto start = std::chrono::system_clock::now();
        auto errAddPolygon = m_osmBaseVisibilityGraph->errBuildVisibilityGraphWithOsm(osmFileName);
        auto end = std::chrono::system_clock::now();
        std::chrono::duration<double> elapsed_seconds = end - start;
        COUT_FILE_LINE_MSG("**** Reading and processing OSM File [" << osmFileName << "] ****");


        m_osmBaseVisibilityGraph = std::make_shared<n_FrameworkLib::CVisibilityGraph>();
#ifdef STEVETEST
        if (errAddPolygon == n_FrameworkLib::CVisibilityGraph::errNoError)
        {
            errAddPolygon = m_osmBaseVisibilityGraph->errInitializeGraphBase();
            if (errAddPolygon != n_FrameworkLib::CVisibilityGraph::errNoError)
            {
                CERR_FILE_LINE_MSG("Error:: initializing base visibility graph for OSM file[" << osmFileName << "].")
            } //if(errAddPolygon == errNoError)
        }
        else //if(errAddPolygon == errNoError)
        {
            CERR_FILE_LINE_MSG("Error:: building base visibility graph for OSM file[" << osmFileName << "].")
        }
#endif  //STEVETEST
        COUT_FILE_LINE_MSG(" **** Finished reading and processing OSM File Elapsed Seconds[" << elapsed_seconds.count() << "] ****");
    }
    if (!ndComponent.attribute(STRING_XML_MINIMUM_WAYPOINT_SEPARATION_M).empty())
    {
        m_minimumWaypointSeparation_m = ndComponent.attribute(STRING_XML_MINIMUM_WAYPOINT_SEPARATION_M).as_double();
    }

    addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
    addSubscriptionAddress(afrl::cmasi::OperatingRegion::Subscription);

    addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
    addSubscriptionAddress(afrl::impact::GroundVehicleConfiguration::Subscription);
    addSubscriptionAddress(afrl::impact::SurfaceVehicleConfiguration::Subscription);

    // service 'global' path planning requests (system assumes aircraft)
    addSubscriptionAddress(uxas::messages::route::RoutePlanRequest::Subscription);
    
    // requests directed to an aircraft planner should also be handled
    addSubscriptionAddress(uxas::common::MessageGroup::AircraftPathPlanner());

    if (m_isRoutAggregator)
    {
        addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
        addSubscriptionAddress(afrl::impact::GroundVehicleState::Subscription);
        addSubscriptionAddress(afrl::impact::SurfaceVehicleState::Subscription);
        addSubscriptionAddress(uxas::messages::route::RouteRequest::Subscription);
    }

    //return (isSucceeded);
}

void rpvs_processReceivedLmcpMessage()
{
    __COPPER_HANDSHAKE__("process");
    if (afrl::cmasi::isAirVehicleConfiguration(receivedLmcpMessage->m_object.get()))
    {
        auto entityConfiguration = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        __COPPER_HANDSHAKE__("air_vehicle_configuration");
        m_idVsEntityConfiguration[entityConfiguration->getID()] = entityConfiguration;
        calculatePlannerParameters(entityConfiguration);
    }
    else if (afrl::impact::isGroundVehicleConfiguration(receivedLmcpMessage->m_object.get()))
    {
        auto entityConfiguration = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        __COPPER_HANDSHAKE__("ground_vehicle_configuration");
        m_idVsEntityConfiguration[entityConfiguration->getID()] = entityConfiguration;
        calculatePlannerParameters(entityConfiguration);
    }
    else if (afrl::impact::isSurfaceVehicleConfiguration(receivedLmcpMessage->m_object.get()))
    {
        auto entityConfiguration = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
        __COPPER_HANDSHAKE__("surface_vehicle_configuration");
        m_idVsEntityConfiguration[entityConfiguration->getID()] = entityConfiguration;
        calculatePlannerParameters(entityConfiguration);
    }
    else if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object.get()))
    {
        auto entityState = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        __COPPER_HANDSHAKE__("air_vehicle_state");
        m_idVsEntityState[entityState->getID()] = entityState;
    }
    else if (afrl::impact::isGroundVehicleState(receivedLmcpMessage->m_object.get()))
    {
        auto entityState = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        __COPPER_HANDSHAKE__("ground_vehicle_state");
        m_idVsEntityState[entityState->getID()] = entityState;
    }
    else if (afrl::impact::isSurfaceVehicleState(receivedLmcpMessage->m_object.get()))
    {
        auto entityState = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
        __COPPER_HANDSHAKE__("surface_vehicle_state");
        m_idVsEntityState[entityState->getID()] = entityState;
    }
    else if (afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
    {
        __COPPER_HANDSHAKE__("keep_in_zone");
        bProcessZone(std::static_pointer_cast<afrl::cmasi::AbstractZone>(receivedLmcpMessage->m_object), true);
    }
    else if (afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
    {
        __COPPER_HANDSHAKE__("keep_out_zone");
        bProcessZone(std::static_pointer_cast<afrl::cmasi::AbstractZone>(receivedLmcpMessage->m_object), false);
    }
    else if (afrl::cmasi::isOperatingRegion(receivedLmcpMessage->m_object.get()))
    {
        __COPPER_HANDSHAKE__("operating_region");
        bProcessOperatingRegion(std::static_pointer_cast<afrl::cmasi::OperatingRegion>(receivedLmcpMessage->m_object));
    }
    else if (uxas::messages::route::isRouteRequest(receivedLmcpMessage->m_object.get()))
    {
        __COPPER_HANDSHAKE__("route_request");
        bProcessRouteRequest(std::static_pointer_cast<uxas::messages::route::RouteRequest>(receivedLmcpMessage->m_object));
    }
    else if (uxas::messages::route::isRoutePlanRequest(receivedLmcpMessage->m_object.get()))
    {
        auto request = std::static_pointer_cast<uxas::messages::route::RoutePlanRequest>(receivedLmcpMessage->m_object);
        auto itEntityConfiguration = m_idVsEntityConfiguration.find(request->getVehicleID());
        __COPPER_HANDSHAKE__("route_plan_request");
        if (itEntityConfiguration != m_idVsEntityConfiguration.end() &&
                (afrl::cmasi::isAirVehicleConfiguration(itEntityConfiguration->second.get()) ||
                afrl::impact::isSurfaceVehicleConfiguration(itEntityConfiguration->second.get())))
        {
            auto routePlanResponse = std::make_shared<uxas::messages::route::RoutePlanResponse>();
            if (bProcessRoutePlanRequest(request, routePlanResponse))
            {
                auto message = std::static_pointer_cast<avtas::lmcp::Object>(routePlanResponse);
                // always limited-cast route plan responses
                sendSharedLmcpObjectLimitedCastMessage(
                        getNetworkClientUnicastAddress(
                            receivedLmcpMessage->m_attributes->getSourceEntityId(),
                            receivedLmcpMessage->m_attributes->getSourceServiceId()
                        ),
                        message);
                __COPPER_HANDSHAKE__("route_plan_response");
            }
        }
    }
    else
    {
      //CERR_FILE_LINE_MSG("WARNING::Unknown Message Type Encountered receivedLmcpMessage->m_object->getLmcpTypeName()[" << receivedLmcpMessage->m_object->getLmcpTypeName() << "]")
    }
    //return (false); // always false implies never terminating service from here
}

void rpvs_service()
{
  rpvs_configure();
  while(1)
      rpvs_processReceivedLmcpMessage();
}


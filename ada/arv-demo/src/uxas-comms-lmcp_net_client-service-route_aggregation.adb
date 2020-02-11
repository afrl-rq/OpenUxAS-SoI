with DOM.Core.Elements;
with UxAS.Messages.Lmcptask.UniqueAutomationRequest; use UxAS.Messages.Lmcptask.UniqueAutomationRequest;
with UxAS.Messages.Lmcptask.TaskPlanOptions;         use UxAS.Messages.Lmcptask.TaskPlanOptions;
with UxAS.Messages.Route.RouteRequest;               use UxAS.Messages.Route.RouteRequest;
with UxAS.Messages.Route.RoutePlanResponse;          use UxAS.Messages.Route.RoutePlanResponse;
with AFRL.CMASI.EntityConfiguration;                 use AFRL.CMASI.EntityConfiguration;
with AFRL.CMASI.EntityState;                         use AFRL.CMASI.EntityState;

with Ada.Characters.Handling;

package body UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation is

   ---------------------------------
   -- Registry_Service_Type_Names --
   ---------------------------------

   function Registry_Service_Type_Names return Service_Type_Names_List is
      (Service_Type_Names_List'(1 => Instance (Service_Type_Name_Max_Length, Content => Type_Name)));

   ------------
   -- Create --
   ------------

   type Route_Aggregator_Service_Ref is access all Route_Aggregator_Service;

   function Create return Any_Service is
      Result : Route_Aggregator_Service_Ref;
   begin
      Result := new Route_Aggregator_Service;
      Result.Construct_Service
        (Service_Type        => Type_Name,
         Work_Directory_Name => Directory_Name);
      return Any_Service (Result);
   end Create;

   ---------------
   -- Configure --
   ---------------

   overriding
   procedure Configure
     (This     : in out Route_Aggregator_Service;
      XML_Node : DOM.Core.Element;
      Result   : out Boolean)
   is
      Unused : boolean;
   begin
      --  if (!ndComponent.attribute(STRING_XML_FAST_PLAN).empty())
      --  {
      --      // Only supported parameter: disables local route planner for
      --      // computationally expensive ground route calculations
      --      m_fastPlan = ndComponent.attribute(STRING_XML_FAST_PLAN).as_bool();
      --  }
      declare
         Attr_Value : constant String := DOM.Core.Elements.Get_Attribute (XML_Node, Name => "FastPlan");
         use Ada.Characters.Handling;
      begin
         if Attr_Value = "" then
            This.Config.M_FastPlan := False;
         elsif To_Lower (Attr_Value) = "true" then
            This.Config.M_FastPlan := True;
         elsif To_Lower (Attr_Value) = "false" then
            This.Config.M_FastPlan := False;
         else -- malformed boolean value
            Result := False;
            return;
         end if;
      end;

      --  track states and configurations for assignment cost matrix calculation
      --  [EntityStates] are used to calculate costs from current position to first task
      --  [EntityConfigurations] are used for nominal speed values (all costs are in terms of time to arrive)

      --  addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.EntityConfiguration.Subscription, Unused);
      for Descendant of EntityConfiguration_Descendants loop
         This.Add_Subscription_Address (Descendant, Unused);
      end loop;

      --  addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.EntityState.Subscription, Unused);
      for Descendant of EntityState_Descendants loop
         This.Add_Subscription_Address (Descendant, Unused);
      end loop;

      --  track requests to kickoff matrix calculation
      --  addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
      This.Add_Subscription_Address (UxAS.Messages.Lmcptask.UniqueAutomationRequest.Subscription, Unused);

      --  subscribe to task plan options to build matrix
      --  addSubscriptionAddress(uxas::messages::task::TaskPlanOptions::Subscription);
      This.Add_Subscription_Address (UxAS.Messages.Lmcptask.TaskPlanOptions.Subscription, Unused);

      --  handle batch route requests
      --  addSubscriptionAddress(uxas::messages::route::RouteRequest::Subscription);
      This.Add_Subscription_Address (UxAS.Messages.Route.RouteRequest.Subscription, Unused);

      --  listen for responses to requests from route planner(s)
      --  addSubscriptionAddress(uxas::messages::route::RoutePlanResponse::Subscription);
      This.Add_Subscription_Address (UxAS.Messages.Route.RoutePlanResponse.Subscription, Unused);

      --  // Subscribe to group messages (whisper from local route planner)
      --  //TODO REVIEW DESIGN "RouteAggregator" "RoutePlanner" flip message addressing effecting session behavior

      --  return true; // may not have the proper fast plan value, but proceed anyway
      Result := True;
   end Configure;

   ----------------
   -- Initialize --
   ----------------

   overriding
   procedure Initialize
     (This : in out Route_Aggregator_Service; Result : out Boolean)
   is
      pragma Unreferenced (This);
   begin
      Result := True; --  per the C++ version
   end Initialize;

   -----------------------------------
   -- Process_Received_LMCP_Message --
   -----------------------------------

   overriding
   procedure Process_Received_LMCP_Message
     (This             : in out Route_Aggregator_Service;
      Received_Message :        not null Any_LMCP_Message;
      Should_Terminate :    out Boolean)
   is
   begin
      pragma Compile_Time_Warning (Standard.True,
         "Process_Received_LMCP_Message unimplemented");
      raise Program_Error
        with "Unimplemented procedure Process_Received_LMCP_Message";

      --  // successful de-serialization of message
      --  if (uxas::messages::route::isRoutePlanResponse(receivedLmcpMessage->m_object.get()))
      --  {
      --      auto rplan = std::static_pointer_cast<uxas::messages::route::RoutePlanResponse>(receivedLmcpMessage->m_object);
      --      m_routePlanResponses[rplan->getResponseID()] = rplan;
      --      for (auto p : rplan->getRouteResponses())
      --      {
      --          m_routePlans[p->getRouteID()] = std::make_pair(rplan->getResponseID(), std::shared_ptr<uxas::messages::route::RoutePlan>(p->clone()));
      --      }
      --      CheckAllRoutePlans();
      --  }
      --  else if (uxas::messages::route::isRouteRequest(receivedLmcpMessage->m_object.get()))
      --  {
      --      auto rreq = std::static_pointer_cast<uxas::messages::route::RouteRequest>(receivedLmcpMessage->m_object);
      --      HandleRouteRequest(rreq);
      --  }
      --  else if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpMessage->m_object))
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
      --      m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
      --      m_airVehicles.insert(id);
      --  }
      --  else if (afrl::vehicles::isGroundVehicleState(receivedLmcpMessage->m_object.get()))
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
      --      m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
      --      m_groundVehicles.insert(id);
      --  }
      --  else if (afrl::vehicles::isSurfaceVehicleState(receivedLmcpMessage->m_object.get()))
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
      --      m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
      --      m_surfaceVehicles.insert(id);
      --  }
      --  else if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(receivedLmcpMessage->m_object))
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
      --      m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
      --      m_airVehicles.insert(id);
      --  }
      --  else if (afrl::vehicles::isGroundVehicleConfiguration(receivedLmcpMessage->m_object.get()))
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
      --      m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
      --      m_groundVehicles.insert(id);
      --  }
      --  else if (afrl::vehicles::isSurfaceVehicleConfiguration(receivedLmcpMessage->m_object.get()))
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
      --      m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
      --      m_surfaceVehicles.insert(id);
      --  }
      --  else if (uxas::messages::task::isUniqueAutomationRequest(receivedLmcpMessage->m_object.get()))
      --  {
      --      auto areq = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage->m_object);
      --      m_uniqueAutomationRequests[m_autoRequestId++] = areq;
      --      //ResetTaskOptions(areq); // clear m_taskOptions and wait for refresh from tasks
      --      CheckAllTaskOptionsReceived();
      --  }
      --  else if (afrl::impact::isImpactAutomationRequest(receivedLmcpMessage->m_object.get()))
      --  {
      --      auto sreq = std::static_pointer_cast<afrl::impact::ImpactAutomationRequest>(receivedLmcpMessage->m_object);
      --      auto areq = std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>();
      --      areq->setOriginalRequest(sreq->getTrialRequest()->clone());
      --      m_uniqueAutomationRequests[m_autoRequestId++] = areq;
      --      areq->setRequestID(m_autoRequestId);
      --      //ResetTaskOptions(areq); // clear m_taskOptions and wait for refresh from tasks
      --      CheckAllTaskOptionsReceived();
      --  }
      --  else if (uxas::messages::task::isTaskPlanOptions(receivedLmcpMessage->m_object.get()))
      --  {
      --      auto taskOptions = std::static_pointer_cast<uxas::messages::task::TaskPlanOptions>(receivedLmcpMessage->m_object);
      --      m_taskOptions[taskOptions->getTaskID()] = taskOptions;
      --      CheckAllTaskOptionsReceived();
      --  }
      --
      --  return (false); // always false implies never terminating service from here
   end Process_Received_LMCP_Message;

   -----------------------------
   -- Package Executable Part --
   -----------------------------

   --  This is the executable part for the package, invoked automatically and only once.
begin
   --  All concrete service subclasses must call this procedure in their
   --  own package like this, with their own params.
   Register_Service_Creation_Function_Pointers (Registry_Service_Type_Names, Create'Access);
end UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation;

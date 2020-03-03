with DOM.Core.Elements;

with UxAS.Messages.Route.RouteRequest;          use UxAS.Messages.Route.RouteRequest;
with UxAS.Messages.Route.RoutePlanResponse;     use UxAS.Messages.Route.RoutePlanResponse;
with AFRL.CMASI.AirVehicleState;                use AFRL.CMASI.AirVehicleState;
with AFRL.Vehicles.GroundVehicleState;          use AFRL.Vehicles.GroundVehicleState;
with AFRL.Vehicles.SurfaceVehicleState;         use AFRL.Vehicles.SurfaceVehicleState;
with AFRL.CMASI.AirVehicleConfiguration;        use AFRL.CMASI.AirVehicleConfiguration;
with AFRL.Vehicles.GroundVehicleConfiguration;  use AFRL.Vehicles.GroundVehicleConfiguration;
with AFRL.Vehicles.SurfaceVehicleConfiguration; use AFRL.Vehicles.SurfaceVehicleConfiguration;
with AFRL.Impact.ImpactAutomationRequest;       use AFRL.Impact.ImpactAutomationRequest;
with AFRL.CMASI.AutomationRequest;              use AFRL.CMASI.AutomationRequest;
with Avtas.Lmcp.Types;

with Ada.Characters.Handling;
with Route_Aggregator_Message_Conversions;

with Ada.Text_IO; use Ada.Text_IO; -- temporarily
--  with Route_Aggregator_Common;

package body UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation is

   procedure Handle_RoutePlanResponse_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : RoutePlanResponse_Any);

   procedure Handle_RouteRequest_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : RouteRequest_Any);

   procedure Handle_AirVehicleState_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityState_Any);

   procedure Handle_GroundVehicleState_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityState_Any);

   procedure Handle_SurfaceVehicleState_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityState_Any);

   procedure Handle_AirVehicleConfig_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityConfiguration_Any);

   procedure Handle_GroundVehicleConfig_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityConfiguration_Any);

   procedure Handle_SurfaceVehicleConfig_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityConfiguration_Any);

   procedure Handle_UniqueAutomationRequest_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : UniqueAutomationRequest_Any);

   procedure Handle_ImpactAutomationRequest_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : ImpactAutomationRequest_Any);

   procedure Handle_TaskPlanOptions_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : TaskPlanOptions_Any);

   ---------------------------------
   -- Registry_Service_Type_Names --
   ---------------------------------

   function Registry_Service_Type_Names return Service_Type_Names_List is
      (Service_Type_Names_List'(1 => Instance (Service_Type_Name_Max_Length, Content => Type_Name)));

   ------------
   -- Create --
   ------------

   function Create return Any_Service is
      Result : Any_Service;
   begin
      Result := new Route_Aggregator_Service;
      Result.Construct_Service
        (Service_Type        => Type_Name,
         Work_Directory_Name => Directory_Name);
      return Result;
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
            This.Config.M_FastPlan := False;  -- FastPlan is an optional parameter
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
Put_Line ("Route_Aggregator_Service processing a received LMCP message");

      --  if (uxas::messages::route::isRoutePlanResponse(receivedLmcpMessage->m_object.get()))
      if Received_Message.Payload.all in RoutePlanResponse'Class then
         This.Handle_RoutePlanResponse_Msg (RoutePlanResponse_Any (Received_Message.Payload));

      --  else if (uxas::messages::route::isRouteRequest(receivedLmcpMessage->m_object.get()))
      elsif Received_Message.Payload.all in RouteRequest'Class then
         This.Handle_RouteRequest_Msg (RouteRequest_Any (Received_Message.Payload));

      --  else if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpMessage->m_object))
      elsif Received_Message.Payload.all in AirVehicleState'Class then
         This.Handle_AirVehicleState_Msg (EntityState_Any (Received_Message.Payload));

      --  else if (afrl::vehicles::isGroundVehicleState(receivedLmcpMessage->m_object.get()))
      elsif Received_Message.Payload.all in GroundVehicleState'Class then
         This.Handle_GroundVehicleState_Msg (EntityState_Any (Received_Message.Payload));

      --  else if (afrl::vehicles::isSurfaceVehicleState(receivedLmcpMessage->m_object.get()))
      elsif Received_Message.Payload.all in SurfaceVehicleState'Class then
         This.Handle_SurfaceVehicleState_Msg (EntityState_Any (Received_Message.Payload));

      --  else if (std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(receivedLmcpMessage->m_object))
      elsif Received_Message.Payload.all in AirVehicleConfiguration'Class then
         This.Handle_AirVehicleConfig_Msg (EntityConfiguration_Any (Received_Message.Payload));

      --  else if (afrl::vehicles::isGroundVehicleConfiguration(receivedLmcpMessage->m_object.get()))
      elsif Received_Message.Payload.all in GroundVehicleConfiguration'Class then
         This.Handle_GroundVehicleConfig_Msg (EntityConfiguration_Any (Received_Message.Payload));

      --  else if (afrl::vehicles::isSurfaceVehicleConfiguration(receivedLmcpMessage->m_object.get()))
      elsif Received_Message.Payload.all in SurfaceVehicleConfiguration'Class then
         This.Handle_SurfaceVehicleConfig_Msg (EntityConfiguration_Any (Received_Message.Payload));

      --  else if (uxas::messages::task::isUniqueAutomationRequest(receivedLmcpMessage->m_object.get()))
      elsif Received_Message.Payload.all in UniqueAutomationRequest'Class then
         This.Handle_UniqueAutomationRequest_Msg (UniqueAutomationRequest_Any (Received_Message.Payload));

      --  else if (afrl::impact::isImpactAutomationRequest(receivedLmcpMessage->m_object.get()))
      elsif Received_Message.Payload.all in ImpactAutomationRequest'Class then
         This.Handle_ImpactAutomationRequest_Msg (ImpactAutomationRequest_Any (Received_Message.Payload));

      --  else if (uxas::messages::task::isTaskPlanOptions(receivedLmcpMessage->m_object.get()))
      elsif Received_Message.Payload.all in TaskPlanOptions'Class then
         This.Handle_TaskPlanOptions_Msg (TaskPlanOptions_Any (Received_Message.Payload));
      end if;

      --  return (false); // always false implies never terminating service from here
      Should_Terminate := False;
   end Process_Received_LMCP_Message;

   ----------------------------------
   -- Handle_RoutePlanResponse_Msg --
   ----------------------------------

   procedure Handle_RoutePlanResponse_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : RoutePlanResponse_Any)
   is
      use Route_Aggregator_Message_Conversions;
   begin
      Route_Aggregator.Handle_Route_Plan_Response (This.Mailbox, This.State, As_RoutePlanResponse_Message (Msg));
   end Handle_RoutePlanResponse_Msg;

   -----------------------------
   -- Handle_RouteRequest_Msg --
   -----------------------------

   procedure Handle_RouteRequest_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : RouteRequest_Any)
   is
      use Route_Aggregator_Message_Conversions;
   begin
      Route_Aggregator.Handle_Route_Request (This.Config, This.Mailbox, This.State, As_RouteRequest_Message (Msg));
   end Handle_RouteRequest_Msg;

   --------------------------------
   -- Handle_AirVehicleState_Msg --
   --------------------------------

   procedure Handle_AirVehicleState_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityState_Any)
   is
      Id : constant Route_Aggregator_Common.Int64 := Route_Aggregator_Common.Int64 (Msg.GetID);
   begin
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
      --      m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
      --      m_airVehicles.insert(id);
      --  }
      This.Config.M_EntityStates := Route_Aggregator_Common.Add (This.Config.M_EntityStates, Id);
      -- we will use the Id values in M_EntityStates to access the pointer values in Entity_Mapping
      This.Entity_Mapping (Id) := Msg;
      This.Config.M_AirVehicles := Add (This.Config.M_AirVehicles, Id);
   end Handle_AirVehicleState_Msg;

   -----------------------------------
   -- Handle_GroundVehicleState_Msg --
   -----------------------------------

   procedure Handle_GroundVehicleState_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityState_Any)
   is
      Id : constant Route_Aggregator_Common.Int64 := Route_Aggregator_Common.Int64 (Msg.GetID);
   begin
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
      --      m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
      --      m_groundVehicles.insert(id);
      --  }
      This.Config.M_EntityStates := Route_Aggregator_Common.Add (This.Config.M_EntityStates, Id);
      -- we will use the Id values in M_EntityStates to access the pointer values in Entity_Mapping
      This.Entity_Mapping (Id) := Msg;
      This.Config.M_GroundVehicles := Add (This.Config.M_GroundVehicles, Id);
   end Handle_GroundVehicleState_Msg;

   ------------------------------------
   -- Handle_SurfaceVehicleState_Msg --
   ------------------------------------

   procedure Handle_SurfaceVehicleState_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityState_Any)
   is
      Id : constant Route_Aggregator_Common.Int64 := Route_Aggregator_Common.Int64 (Msg.GetID);
   begin
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object)->getID();
      --      m_entityStates[id] = std::static_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
      --      m_surfaceVehicles.insert(id);
      --  }
      This.Config.M_EntityStates := Route_Aggregator_Common.Add (This.Config.M_EntityStates, Id);
      -- we will use the Id values in M_EntityStates to access the pointer values in Entity_Mapping
      This.Entity_Mapping (Id) := Msg;
      This.Config.M_SurfaceVehicles := Add (This.Config.M_SurfaceVehicles, Id);
   end Handle_SurfaceVehicleState_Msg;

   ---------------------------------
   -- Handle_AirVehicleConfig_Msg --
   ---------------------------------

   procedure Handle_AirVehicleConfig_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityConfiguration_Any)
   is
      Id : constant Route_Aggregator_Common.Int64 := Route_Aggregator_Common.Int64 (Msg.GetID);
   begin
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
      --      m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
      --      m_airVehicles.insert(id);
      --  }
      This.Entity_Configurations (Id) := Msg;
      This.Config.M_AirVehicles := Add (This.Config.M_AirVehicles, Id);
   end Handle_AirVehicleConfig_Msg;

   ------------------------------------
   -- Handle_GroundVehicleConfig_Msg --
   ------------------------------------

   procedure Handle_GroundVehicleConfig_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityConfiguration_Any)
   is
      Id : constant Route_Aggregator_Common.Int64 := Route_Aggregator_Common.Int64 (Msg.GetID);
   begin
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
      --      m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
      --      m_groundVehicles.insert(id);
      --  }
      This.Entity_Configurations (Id) := Msg;
      This.Config.M_GroundVehicles := Add (This.Config.M_GroundVehicles, Id);
      end Handle_GroundVehicleConfig_Msg;

   -------------------------------------
   -- Handle_SurfaceVehicleConfig_Msg --
   -------------------------------------

   procedure Handle_SurfaceVehicleConfig_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : EntityConfiguration_Any)
   is
      Id : constant Route_Aggregator_Common.Int64 := Route_Aggregator_Common.Int64 (Msg.GetID);
   begin
      --  {
      --      int64_t id = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object)->getID();
      --      m_entityConfigurations[id] = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
      --      m_surfaceVehicles.insert(id);
      --  }
      This.Entity_Configurations (Id) := Msg;
      This.Config.M_SurfaceVehicles := Add (This.Config.M_SurfaceVehicles, Id);
   end Handle_SurfaceVehicleConfig_Msg;

   ----------------------------------------
   -- Handle_UniqueAutomationRequest_Msg --
   ----------------------------------------

   procedure Handle_UniqueAutomationRequest_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : UniqueAutomationRequest_Any)
   is
   begin
      --  {
      --      auto areq = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage->m_object);
      --      m_uniqueAutomationRequests[m_autoRequestId++] = areq;
      --      //ResetTaskOptions(areq); // clear m_taskOptions and wait for refresh from tasks
      --      CheckAllTaskOptionsReceived();
      --  }
      This.M_AutoRequestId := This.M_AutoRequestId + 1;
      This.M_UniqueAutomationRequests (This.M_AutoRequestId) := Msg;
      This.Check_All_Task_Options_Received;
   end Handle_UniqueAutomationRequest_Msg;

   ----------------------------------------
   -- Handle_ImpactAutomationRequest_Msg --
   ----------------------------------------

   procedure Handle_ImpactAutomationRequest_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : ImpactAutomationRequest_Any)
   is
      AReq : constant UniqueAutomationRequest_Any := new UniqueAutomationRequest;
   begin
      --  {
      --      auto sreq = std::static_pointer_cast<afrl::impact::ImpactAutomationRequest>(receivedLmcpMessage->m_object);
      --      auto areq = std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>();
      --
      --      areq->setOriginalRequest(sreq->getTrialRequest()->clone());
      --      m_uniqueAutomationRequests[m_autoRequestId++] = areq;
      --      areq->setRequestID(m_autoRequestId);
      --      //ResetTaskOptions(areq); // clear m_taskOptions and wait for refresh from tasks
      --      CheckAllTaskOptionsReceived();
      --  }
      AReq.SetOriginalRequest (new AutomationRequest'(Msg.GetTrialRequest.all));
      This.M_AutoRequestId := This.M_AutoRequestId + 1;
      This.M_UniqueAutomationRequests (This.M_AutoRequestId) := AReq;
      AReq.SetRequestID (Avtas.Lmcp.Types.Int64 (This.M_AutoRequestId));
      This.Check_All_Task_Options_Received;
   end Handle_ImpactAutomationRequest_Msg;

   --------------------------------
   -- Handle_TaskPlanOptions_Msg --
   --------------------------------

   procedure Handle_TaskPlanOptions_Msg
     (This : in out Route_Aggregator_Service;
      Msg  : TaskPlanOptions_Any)
   is
      Id : constant Route_Aggregator_Common.Int64 := Route_Aggregator_Common.Int64 (Msg.GetTaskID);
   begin
      --  {
      --      auto taskOptions = std::static_pointer_cast<uxas::messages::task::TaskPlanOptions>(receivedLmcpMessage->m_object);
      --      m_taskOptions[taskOptions->getTaskID()] = taskOptions;
      --      CheckAllTaskOptionsReceived();
      --  }
      This.M_TaskOptions (Id) := Msg;
      This.Check_All_Task_Options_Received;
   end Handle_TaskPlanOptions_Msg;

   -------------------------------------
   -- Check_All_Task_Options_Received --
   -------------------------------------

   procedure BuildMatrixRequests
     (Key : Route_Aggregator_Common.Int64;
      Msg : UniqueAutomationRequest_Any);

   procedure Check_All_Task_Options_Received
     (This : in out Route_Aggregator_Service)
   is
      AllReceived : Boolean;
      TaskId : AVTAS.LMCP.Types.Int64;
      C : Id_UniqueAutomationRequest_Mapping.Cursor;
      AReq : UniqueAutomationRequest_Any;
   begin
      --  // loop through all automation requests; delete when fulfilled
      --  auto areqIter = m_uniqueAutomationRequests.begin();
      --  while (areqIter != m_uniqueAutomationRequests.end())

      --  for AReq : UniqueAutomationRequest_Any of This.M_UniqueAutomationRequests loop
      C := Id_UniqueAutomationRequest_Mapping.First (This.M_UniqueAutomationRequests);
      while Id_UniqueAutomationRequest_Mapping.Has_Element (C) loop
         AReq := Id_UniqueAutomationRequest_Mapping.Element (C);

         --  check that to see if all options from all tasks have been received for this request
         AllReceived := True;
         --  for (size_t t = 0; t < areqIter->second->getOriginalRequest()->getTaskList().size(); t++)
         for T in Ada.Containers.Count_Type range 0 .. afrl.cmasi.AutomationRequest.Vect_Int64.Length (AReq.getOriginalRequest.getTaskList.all) loop
            --  int64_t taskId = areqIter->second->getOriginalRequest()->getTaskList().at(t);
            TaskId := AFRL.CMASI.AutomationRequest.Vect_Int64.Element (AReq.GetOriginalRequest.GetTaskList.all, Natural (T));

            --  if (m_taskOptions.find(taskId) == m_taskOptions.end())
            if not Id_TaskPlanOptions_Mapping.Contains (This.M_TaskOptions, Route_Aggregator_Common.Int64 (TaskId)) then
               AllReceived := False;
               exit;
            end if;
         end loop;

         if AllReceived then
            --  Build messages for matrix
            --  BuildMatrixRequests(areqIter->first, areqIter->second);
            BuildMatrixRequests (Key => Id_UniqueAutomationRequest_Mapping.Key (C),
                                 Msg => Id_UniqueAutomationRequest_Mapping.Element (C));
         end if;

         Id_UniqueAutomationRequest_Mapping.Next (C);
      end loop;
   end Check_All_Task_Options_Received;

   -------------------------
   -- BuildMatrixRequests --
   -------------------------

   procedure BuildMatrixRequests
     (Key : Route_Aggregator_Common.Int64;
      Msg : UniqueAutomationRequest_Any)
   is
   begin
      null;
   end BuildMatrixRequests;

   -----------------------------
   -- Package Executable Part --
   -----------------------------

   --  This is the executable part for the package, invoked automatically and only once.
begin
   --  All concrete service subclasses must call this procedure in their
   --  own package like this, with their own params.
   Register_Service_Creation_Function_Pointers (Registry_Service_Type_Names, Create'Access);
end UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation;

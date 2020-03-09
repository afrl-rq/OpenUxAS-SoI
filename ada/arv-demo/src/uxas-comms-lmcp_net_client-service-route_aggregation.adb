with Ada.Text_IO; use Ada.Text_IO; -- temporarily

with Ada.Containers.Vectors;
with DOM.Core.Elements;
with Ada.Characters.Handling;
with Route_Aggregator_Message_Conversions;

with UxAS.Messages.Route.RouteRequest;          use UxAS.Messages.Route.RouteRequest;
with UxAS.Messages.Route.RoutePlanRequest;      use UxAS.Messages.Route.RoutePlanRequest;
with UxAS.Messages.Route.RoutePlanResponse;     use UxAS.Messages.Route.RoutePlanResponse;
with UxAS.Messages.LMCPTASK.PlanningState;      use UxAS.Messages.LMCPTASK.PlanningState;
with UxAS.Messages.LMCPTASK.TaskOption;
with UXAS.Messages.Route.RouteConstraints;
with AFRL.Vehicles.GroundVehicleState;          use AFRL.Vehicles.GroundVehicleState;
with AFRL.Vehicles.SurfaceVehicleState;         use AFRL.Vehicles.SurfaceVehicleState;
with AFRL.Vehicles.GroundVehicleConfiguration;  use AFRL.Vehicles.GroundVehicleConfiguration;
with AFRL.Vehicles.SurfaceVehicleConfiguration; use AFRL.Vehicles.SurfaceVehicleConfiguration;
with AFRL.Impact.ImpactAutomationRequest;       use AFRL.Impact.ImpactAutomationRequest;
with AFRL.CMASI.AirVehicleConfiguration;        use AFRL.CMASI.AirVehicleConfiguration;
with AFRL.CMASI.AutomationRequest;              use AFRL.CMASI.AutomationRequest;
with AFRL.CMASI.Location3D;                     use AFRL.CMASI.Location3D;
with AFRL.CMASI.AirVehicleState;                use AFRL.CMASI.AirVehicleState;

with UxAS.Common.String_Constant.Message_Group;

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

   procedure Check_All_Route_Plans
     (This : in out Route_Aggregator_Service);

   package RoutePlanRequest_Sequences is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => RoutePlanRequest_Any);

   procedure Euclidian_Plan
     (This : in out Route_Aggregator_Service;
      Plan : RoutePlanRequest_Any);

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
      --  Id : constant Route_Aggregator_Common.Int64 := Route_Aggregator_Common.Int64 (Msg.GetTaskID);
      Id : constant AVTAS.LMCP.Types.Int64 := Msg.GetTaskID;
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

   procedure Check_All_Task_Options_Received
     (This : in out Route_Aggregator_Service)
   is
      AllReceived : Boolean;
      TaskId      : AVTAS.LMCP.Types.Int64;
      C           : Id_UniqueAutomationRequest_Mapping.Cursor;
      AReq        : UniqueAutomationRequest_Any;
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
            --  if not Id_TaskPlanOptions_Mapping.Contains (This.M_TaskOptions, Route_Aggregator_Common.Int64 (TaskId)) then
            if not Id_TaskPlanOptions_Mapping.Contains (This.M_TaskOptions, TaskId) then
               AllReceived := False;
               exit;
            end if;
         end loop;

         if AllReceived then
            --  Build messages for matrix
            --  BuildMatrixRequests(areqIter->first, areqIter->second);
            This.BuildMatrixRequests (reqId => AVTAS.LMCP.Types.Int64 (Id_UniqueAutomationRequest_Mapping.Key (C)),
                                      AReq  => Id_UniqueAutomationRequest_Mapping.Element (C));
         end if;

         Id_UniqueAutomationRequest_Mapping.Next (C);
      end loop;
   end Check_All_Task_Options_Received;

   -------------------------
   -- BuildMatrixRequests --
   -------------------------

   procedure BuildMatrixRequests
     (This  : in out Route_Aggregator_Service;
      ReqId : AVTAS.LMCP.Types.Int64;
      AReq  : UniqueAutomationRequest_Any)
   is
      --  std::vector< std::shared_ptr<uxas::messages::route::RoutePlanRequest> > sendAirPlanRequest;
      sendAirPlanRequest    : RoutePlanRequest_Sequences.Vector;
      --  std::vector< std::shared_ptr<uxas::messages::route::RoutePlanRequest> > sendGroundPlanRequest;
      sendGroundPlanRequest : RoutePlanRequest_Sequences.Vector;
   begin
      --  pragma Compile_Time_Warning (Standard.True, "BuildMatrixRequests is not implemented");
      --  // All options corresponding to current automation request have been received
      --  // now make 'matrix' requests (all task options to all other task options)
      --  // [but only if options haven't already been sent??]
      --
      --  // Proceedure:
      --  //  1. Create new 'pending' data structure for all routes that will fulfill this request
      --  //  2. For each vehicle, create requests for:
      --  //       a. initial position to each task option
      --  //       b. task/option to task/option
      --  //       c. associate routeID with task options in m_routeTaskPairing
      --  //       d. push routeID onto pending list
      --  //  3. Send requests to proper planners
      --
      --  m_pendingAutoReq[reqId] = std::unordered_set<int64_t>();
      This.M_PendingAutoReq (ReqId) := Int64_Sets.Empty_Set;

      --  std::vector< std::shared_ptr<uxas::messages::route::RoutePlanRequest> > sendAirPlanRequest;
      --  std::vector< std::shared_ptr<uxas::messages::route::RoutePlanRequest> > sendGroundPlanRequest;

      --  // if the 'EntityList' is empty, then ALL vehicles are considered eligible
      --  if(areq->getOriginalRequest()->getEntityList().empty())
      --  {
      --      for(auto entity : m_entityStates)
      --      {
      --          areq->getOriginalRequest()->getEntityList().push_back(entity.second->getID());
      --      }
      --  }
      if AReq.GetOriginalRequest.GetEntityList.Is_Empty then
         for Id : Route_Aggregator_Common.Int64 of This.Config.M_EntityStates loop
            declare
               Entity : EntityState_Any;
            begin
               --  use that Id in This.Entity_Mapping to get the entity state message
               Entity := This.Entity_Mapping (Id);
               AFRL.CMASI.AutomationRequest.Vect_Int64.Append (AReq.GetOriginalRequest.GetEntityList.all, Entity.GetID);
            end;
         end loop;
      end if;

      --  // to minimize network traffic make a separate request for each vehicle
      --  for (size_t v = 0; v < areq->getOriginalRequest()->getEntityList().size(); v++)
      For_Each_Vehicle : for V in Positive range 1 .. Natural (AReq.GetOriginalRequest.GetEntityList.Length) loop
         --  {
         Make_Request : declare
            --  only check vehicles that have valid states

            --      int64_t vehicleId = areq->getOriginalRequest()->getEntityList().at(v);
            VehicleId : constant AVTAS.LMCP.Types.Int64 := AReq.GetOriginalRequest.GetEntityList.Element (V);
            --      auto vehicle = m_entityStates.find(vehicleId);
            VId       : constant Route_Aggregator_Common.Int64 := Route_Aggregator_Common.Int64 (VehicleId);
            VehicleCursor   : constant Id_EntityState_Mapping.Cursor := This.Entity_Mapping.Find (VId);
            --  when we need the corresponding EntityState_Any, we will do the following in effect:
            --  Vehicle   : EntityState_Any := This.Entity_Mapping.Element (VehicleCursor);
            Vehicle   : EntityState_Any;

            --      float startHeading_deg{0.0};
            StartHeading_Deg : AVTAS.LMCP.Types.Real32 := 0.0;
            --      auto startLocation = std::shared_ptr<afrl::cmasi::Location3D>();
            StartLocation : AFRL.CMASI.Location3D.Location3D_Any;
            --      bool isFoundPlannningState{false};
            FoundPlannningState : Boolean := False;

            use type Id_EntityState_Mapping.Cursor;
         begin
            --  for (auto& planningState : areq->getPlanningStates())
            --  {
            --      if (planningState->getEntityID() == vehicleId)
            --      {
            --          startLocation.reset(planningState->getPlanningPosition()->clone());
            --          startHeading_deg = planningState->getPlanningHeading();
            --          isFoundPlannningState = true;
            --          break;
            --      }
            --  }
            for PlanningState of AReq.GetPlanningStates.all loop
               if PlanningState.GetEntityId = VehicleId then
                  StartLocation := new AFRL.CMASI.Location3D.Location3D'(AFRL.CMASI.Location3D.Location3D (PlanningState.GetPlanningPosition.all));
                  StartHeading_Deg := PlanningState.GetPlanningHeading;
                  FoundPlannningState := True;
                  exit;
               end if;
            end loop;

            --  if (isFoundPlannningState || (vehicle != m_entityStates.end()))
            if FoundPlannningState or else VehicleCursor /= Id_EntityState_Mapping.No_Element then
               Build_Eligible_Task_Options : declare

                  package TaskOption_Vectors is new Ada.Containers.Vectors
                    (Index_Type   => Positive,
                     Element_Type => UxAS.Messages.LMCPtask.TaskOption.TaskOption_Any,
                     "=" => UxAS.Messages.LMCPtask.TaskOption."=");

                  --  std::vector<std::shared_ptr<uxas::messages::task::TaskOption> > taskOptionList;
                  TaskOptionList : TaskOption_Vectors.Vector;

                  TaskId : AVTAS.LMCP.Types.Int64;
                  Option : UxAS.Messages.LMCPTASK.TaskOption.TaskOption_Acc;
                  --  Elig   : AVTAS.LMCP.Types.Int64;
                  Found_Elig : Boolean := False;

                  --  std::shared_ptr<uxas::messages::route::RoutePlanRequest> planRequest(new uxas::messages::route::RoutePlanRequest);
                  PlanRequest : constant RoutePlanRequest_Any := new RoutePlanRequest;

               begin
                  --  for (size_t t = 0; t < areq->getOriginalRequest()->getTaskList().size(); t++)
                  for T in Positive range 1 .. Natural (AReq.GetOriginalRequest.getTaskList.Length) loop
                     --  int64_t taskId = areq->getOriginalRequest()->getTaskList().at(t);
                     TaskId := AReq.GetOriginalRequest.getTaskList.Element (T);
                     --  if (m_taskOptions.find(taskId) != m_taskOptions.end())
                     if This.M_TaskOptions.Contains (TaskId) then
                        -- for (size_t o = 0; o < m_taskOptions[taskId]->getOptions().size(); o++)
                        for K in Natural range 1 .. Natural (This.M_TaskOptions.Element (TaskId).GetOptions.Length) loop
                           --  auto option = m_taskOptions[taskId]->getOptions().at(o);
                           Option := This.M_TaskOptions.Element (taskId).getOptions.Element (K);

                           --  auto elig = std::find_if(option->getEligibleEntities().begin(), option->getEligibleEntities().end(),
                           --                           [&](int64_t v)
                           --                           {
                           --                               return v == vehicleId; });
                           for V of Option.GetEligibleEntities.all loop
                              if V = VehicleId then
                                 --  Elig := V;
                                 Found_Elig := True;
                                 exit;
                              end if;
                           end loop;

                           --  if (option->getEligibleEntities().empty() || elig != option->getEligibleEntities().end())
                           --  {
                           --      taskOptionList.push_back(std::shared_ptr<uxas::messages::task::TaskOption>(option->clone()));
                           --  }
                           if Option.GetEligibleEntities.Is_Empty or else Found_Elig then
                              TaskOption_Vectors.Append (TaskOptionList, new UxAS.Messages.LMCPtask.TaskOption.TaskOption'(Option.all));
                           end if;
                        end loop;
                     end if;
                  end loop;

                  --  // create a new route plan request
                  --  std::shared_ptr<uxas::messages::route::RoutePlanRequest> planRequest(new uxas::messages::route::RoutePlanRequest);
                  --  planRequest->setAssociatedTaskID(0); // mapping from routeID to proper task
                  PlanRequest.setAssociatedTaskID (0);
                  --  planRequest->setIsCostOnlyRequest(false);  // request full path for more accurate timing information
                  PlanRequest.setIsCostOnlyRequest (False);
                  --  planRequest->setOperatingRegion(areq->getOriginalRequest()->getOperatingRegion());
                  PlanRequest.setOperatingRegion (AReq.GetOriginalRequest.getOperatingRegion);
                  --  planRequest->setVehicleID(vehicleId);
                  PlanRequest.setVehicleID (VehicleId);
                  --  //planRequest->setRouteID(m_planrequestId);
                  --  //m_planrequestId++;

                  --  if (!isFoundPlannningState)
                  if not FoundPlannningState then
                     --  assert(vehicle != m_entityStates.end());
                     pragma Assert (Id_EntityState_Mapping.Has_Element (VehicleCursor));
                     Vehicle := This.Entity_Mapping.Element (VId);
                     --  startLocation.reset(vehicle->second->getLocation()->clone());
                     StartLocation := new AFRL.CMASI.Location3D.Location3D'(AFRL.CMASI.Location3D.Location3D (Vehicle.getLocation.all));
                     --  startHeading_deg = vehicle->second->getHeading();
                     StartHeading_Deg := Vehicle.getHeading;
                  end if;

                  --  // find routes from initial conditions
                  --  for (size_t t = 0; t < taskOptionList.size(); t++)
                  for T in Natural range 1 .. Natural (TaskOptionList.Length) loop
                     declare
                        --  auto option = taskOptionList.at(t);
                        Option : constant UxAS.Messages.LMCPTASK.TaskOption.TaskOption_Any := TaskOptionList.Element (T);
                        TOP    : AggregatorTaskOptionPair_Reference;
                        R      : UXAS.Messages.Route.RouteConstraints.RouteConstraints_Any;
                     begin
                        --  // build map from request to full task/option information
                        --  AggregatorTaskOptionPair* top = new AggregatorTaskOptionPair(vehicleId, 0, 0, option->getTaskID(), option->getOptionID());
                        TOP := new AggregatorTaskOptionPair'(VehicleId, 0, 0, Option.getTaskID, Option.getOptionID);
                        --  m_routeTaskPairing[m_routeId] = std::shared_ptr<AggregatorTaskOptionPair>(top);
                        This.M_RouteTaskPairing (This.m_RouteId) := TOP;

                        --  uxas::messages::route::RouteConstraints* r = new uxas::messages::route::RouteConstraints;
                        R := new UXAS.Messages.Route.RouteConstraints.RouteConstraints;
                        --  r->setStartLocation(startLocation->clone());
                        R.setStartLocation (new AFRL.CMASI.Location3d.Location3D'(AFRL.CMASI.Location3d.Location3D (StartLocation.all)));
                        --  r->setStartHeading(startHeading_deg);
                        R.setStartHeading (StartHeading_Deg);
                        --  r->setEndLocation(option->getStartLocation()->clone());
                        R.setEndLocation (new AFRL.CMASI.Location3d.Location3D'(AFRL.CMASI.Location3d.Location3D (StartLocation.all)));
                        --  r->setEndHeading(option->getStartHeading());
                        R.setEndHeading (StartHeading_Deg);
                        --  r->setRouteID(m_routeId);
                        R.SetRouteID (This.M_RouteId);
                        --  planRequest->getRouteRequests().push_back(r);
                        Uxas.Messages.Route.RoutePlanRequest.Vect_RouteConstraints_Acc.Append
                          (PlanRequest.GetRouteRequests.all,
                           UXAS.Messages.Route.RouteConstraints.RouteConstraints_Acc (R));
                        --  m_pendingAutoReq[reqId].insert(m_routeId);
                        This.M_PendingAutoReq (ReqId).Include (This.M_RouteId);
                        --  m_routeId++;
                        This.M_RouteId := This.M_RouteId + 1;
                     end;
                  end loop;

                  --  // found routes between all task options
                  --  for (size_t t1 = 0; t1 < taskOptionList.size(); t1++)
                  for T1 in Natural range 1 .. Natural (TaskOptionList.Length) loop
                     --  for (size_t t2 = 0; t2 < taskOptionList.size(); t2++)
                     for T2 in Natural range 1 .. Natural (TaskOptionList.Length) loop
                        --  if (t1 != t2)
                        if T1 /= T2 then
                           declare
                              --  auto option1 = taskOptionList.at(t1);
                              Option1 : constant UxAS.Messages.LMCPtask.TaskOption.TaskOption_Any := TaskOptionList.Element (T1);
                              --  auto option2 = taskOptionList.at(t2);
                              Option2 : constant UxAS.Messages.LMCPtask.TaskOption.TaskOption_Any := TaskOptionList.Element (T2);
                              TOP     : AggregatorTaskOptionPair_Reference;
                              R       : UXAS.Messages.Route.RouteConstraints.RouteConstraints_Any;
                           begin
                              --  // build map from request to full task/option information
                              --  AggregatorTaskOptionPair* top = new AggregatorTaskOptionPair(vehicleId, option1->getTaskID(), option1->getOptionID(), option2->getTaskID(), option2->getOptionID());
                              TOP := new AggregatorTaskOptionPair'(vehicleId, option1.getTaskID, option1.getOptionID, option2.getTaskID, option2.getOptionID);
                              --  m_routeTaskPairing[m_routeId] = std::shared_ptr<AggregatorTaskOptionPair>(top);
                              This.M_RouteTaskPairing (This.m_routeId) := TOP;

                              --  uxas::messages::route::RouteConstraints* r = new uxas::messages::route::RouteConstraints;
                              R := new UXAS.Messages.Route.RouteConstraints.RouteConstraints;
                              --  r->setStartLocation(option1->getEndLocation()->clone());
                              R.setStartLocation (new AFRL.CMASI.Location3d.Location3D'(AFRL.CMASI.Location3d.Location3D (Option1.getEndLocation.all)));
                              --  r->setStartHeading(option1->getEndHeading());
                              R.setStartHeading (Option1.getEndHeading);
                              --  r->setEndLocation(option2->getStartLocation()->clone());
                              R.setEndLocation (new AFRL.CMASI.Location3d.Location3D'(AFRL.CMASI.Location3d.Location3D (Option2.getStartLocation.all)));
                              --  r->setEndHeading(option2->getStartHeading());
                              R.setEndHeading (Option2.getStartHeading);
                              --  r->setRouteID(m_routeId);
                              R.setRouteID (This.m_routeId);
                              --  planRequest->getRouteRequests().push_back(r);
                              Uxas.Messages.Route.RoutePlanRequest.Vect_RouteConstraints_Acc.Append
                                (PlanRequest.GetRouteRequests.all,
                                 UXAS.Messages.Route.RouteConstraints.RouteConstraints_Acc (R));
                              --  m_pendingAutoReq[reqId].insert(m_routeId);
                                This.M_PendingAutoReq (ReqId).Include (This.M_RouteId);
                              --  m_routeId++;
                              This.M_RouteId := This.M_RouteId + 1;
                           end;
                        end if;
                     end loop;
                  end loop;

                  --  // send this plan request to the prescribed route planner for ground vehicles
                  --  if (m_groundVehicles.find(vehicleId) != m_groundVehicles.end())
                  if Contains (This.Config.M_GroundVehicles, Route_Aggregator_Common.Int64 (VehicleId)) then
                     --  sendGroundPlanRequest.push_back(planRequest);
                     SendGroundPlanRequest.Append (PlanRequest);
                  else
                     --  sendAirPlanRequest.push_back(planRequest);
                     sendAirPlanRequest.Append (PlanRequest);
                  end if;
               end Build_Eligible_Task_Options;
            end if;
         end Make_Request;
      end loop For_Each_Vehicle;

      --  send all requests for aircraft plans
      --  for (size_t k = 0; k < sendAirPlanRequest.size(); k++)
      for K in Natural range 1 .. Natural (SendAirPlanRequest.Length) loop
         --  std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(sendAirPlanRequest.at(k));
         --  sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::AircraftPathPlanner(), pRequest);
         This.Send_LMCP_Object_Limited_Cast_Message
           (UxAS.Common.String_Constant.Message_Group.AircraftPathPlanner,
            Object_Any (SendAirPlanRequest.Element (K)));
      end loop;

      --  send all requests for ground plans
      --  for (size_t k = 0; k < sendGroundPlanRequest.size(); k++)
      for K in Natural range 1 .. Natural (SendGroundPlanRequest.Length) loop
         --  std::shared_ptr<avtas::lmcp::Object> pRequest = std::static_pointer_cast<avtas::lmcp::Object>(sendGroundPlanRequest.at(k));
         --  if (m_fastPlan)
         if This.Config.M_FastPlan then
            --  short-circuit and just plan with straight line planner
            --  EuclideanPlan(sendGroundPlanRequest.at(k));
            This.Euclidian_Plan (SendGroundPlanRequest.Element (K));
         else  --  send externally
            --  sendSharedLmcpObjectLimitedCastMessage(uxas::common::MessageGroup::GroundPathPlanner(), pRequest);
            This.Send_LMCP_Object_Limited_Cast_Message
              (UxAS.Common.String_Constant.Message_Group.GroundPathPlanner,
               Object_Any (SendGroundPlanRequest.Element (K)));
         end if;
      end loop;

      --  // fast planning should be complete, so kick off sending response
      --  if (m_fastPlan)
      if This.config.m_fastPlan then
         --  CheckAllRoutePlans();
         This.Check_All_Route_Plans;
      end if;
   end BuildMatrixRequests;

   --------------------
   -- Euclidian_Plan --
   --------------------

   procedure Euclidian_Plan
     (This : in out Route_Aggregator_Service;
      Plan : RoutePlanRequest_Any)
   is
      use Route_Aggregator_Message_Conversions;
   begin
      Route_Aggregator.Euclidean_Plan
        (Data               => This.Config,
         RoutePlanResponses => This.State.m_routePlanResponses,
         RoutePlans         => This.State.m_routePlans,
         Request            => As_RoutePlanRequest_Message (Plan));
   end Euclidian_Plan;

   ---------------------------
   -- Check_All_Route_Plans --
   ---------------------------

   procedure Check_All_Route_Plans
     (This : in out Route_Aggregator_Service)
   is
   begin
      Route_Aggregator.Check_All_Route_Plans (This.Mailbox, This.State);
   end Check_All_Route_Plans;

   -----------------------------
   -- Package Executable Part --
   -----------------------------

   --  This is the executable part for the package, invoked automatically and only once.
begin
   --  All concrete service subclasses must call this procedure in their
   --  own package like this, with their own params.
   Register_Service_Creation_Function_Pointers (Registry_Service_Type_Names, Create'Access);
end UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation;

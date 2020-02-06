with AVTAS.Lmcp.Object.SPARK_Boundary;              use AVTAS.Lmcp.Object.SPARK_Boundary;

with AFRL.CMASI.Enumerations;
with AFRl.CMASI.AutomationResponse;                 use AFRl.CMASI.AutomationResponse;
with AFRL.CMASI.AutomationRequest;                  use AFRL.CMASI.AutomationRequest;
with AFRL.CMASI.EntityConfiguration;                use AFRL.CMASI.EntityConfiguration;
with AFRL.CMASI.EntityState;                        use AFRL.CMASI.EntityState;
with AFRL.CMASI.LmcpTask;                           use AFRL.CMASI.LmcpTask;
with AFRL.CMASI.KeepInZone;                         use AFRL.CMASI.KeepInZone;
with AFRL.CMASI.KeepOutZone;                        use AFRL.CMASI.KeepOutZone;
with AFRL.CMASI.RemoveTasks;                        use AFRL.CMASI.RemoveTasks;
with AFRL.CMASI.ServiceStatus;                      use AFRL.CMASI.ServiceStatus;
with AFRL.CMASI.KeyValuePair;                       use AFRL.CMASI.KeyValuePair;
with AFRL.CMASI.OperatingRegion;                    use AFRL.CMASI.OperatingRegion;

with AFRL.Impact.ImpactAutomationRequest;           use AFRL.Impact.ImpactAutomationRequest;
with AFRL.Impact.PointOfInterest;                   use AFRL.Impact.PointOfInterest;
with AFRL.Impact.LineOfInterest;                    use AFRL.Impact.LineOfInterest;
with AFRL.Impact.AreaOfInterest;                    use AFRL.Impact.AreaOfInterest;
with AFRL.Impact.ImpactAutomationResponse;          use AFRL.Impact.ImpactAutomationResponse;

with UxAS.Messages.Lmcptask.TaskAutomationRequest;  use UxAS.Messages.Lmcptask.TaskAutomationRequest;
with UxAS.Messages.Lmcptask.TaskAutomationResponse; use UxAS.Messages.Lmcptask.TaskAutomationResponse;
with UxAS.Messages.Lmcptask.TaskInitialized;        use UxAS.Messages.Lmcptask.TaskInitialized;
with UxAS.Messages.Lmcptask.PlanningState;          use UxAS.Messages.Lmcptask.PlanningState;

with UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation.SPARK;

with String_Utils;
with Ada.Strings.Unbounded;

with DOM.Core.Elements;

package body UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation is

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   function Is_Any_Automation_Request (Msg : Object_Any) return Boolean;

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_EntityConfig_Msg
     (This         : in out Automation_Request_Validator_Service;
      EntityConfig : EntityConfiguration_Any);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_StateEntity_Msg
     (This  : in out Automation_Request_Validator_Service;
      State : EntityState_Any);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_InitializedTasks_Msg
     (This : in out Automation_Request_Validator_Service;
      Job  : LmcpTask_Any);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_ServiceStatus_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_RemoveTasks_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_TaskInitialized_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_AreaOfInterest_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_LineOfInterest_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_PointofInterest_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_KeepInZone_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_KeepOutZone_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message);

   --  Refactored out of Process_Received_LMCP_Message for readability, comprehension, etc.
   procedure Handle_OperatingRegion_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message);

   ---------------
   -- Construct --
   ---------------

   procedure Construct
     (This : in out Automation_Request_Validator_Service)
   is
   begin
      This.Construct_Service
        (Service_Type        => Type_Name,
         Work_Directory_Name => Directory_Name);

      --  from the request validator ctor:
      --
      --  make sure error collection is non-null
      --  m_errorResponse.reset(new uxas::messages::task::UniqueAutomationResponse);
      -- This.Error_Response := new UniqueAutomationResponse;
      --
      --  Ada: the component is declared, rather than allocated
      --
      --  if(!m_errorResponse->getOriginalResponse())
      if This.Error_Response.getOriginalResponse = null then
      --  m_errorResponse->setOriginalResponse(new afrl::cmasi::AutomationResponse);
         This.Error_Response.setOriginalResponse (new AutomationResponse);
      end if;
   end Construct;

   ---------------------------------
   -- Registry_Service_Type_Names --
   ---------------------------------

   function Registry_Service_Type_Names return Service_Type_Names_List is
      (Service_Type_Names_List'(1 => Instance (Service_Type_Name_Max_Length, Content => Type_Name)));

   ------------
   -- Create --
   ------------

   function Create return Any_Service is
      Result : Automation_Request_Validator_Service_Ref;
   begin
      Result := new Automation_Request_Validator_Service;
      Result.Construct; -- specific to Ada version
      return Any_Service (Result);
   end Create;

   ---------------
   -- Configure --
   ---------------

   overriding
   procedure Configure
     (This     : in out Automation_Request_Validator_Service;
      XML_Node : DOM.Core.Element;
      Result   : out Boolean)
   is
      Unused : Boolean;
   begin
      --  // configure response time parameter, ensure response time is reasonable
      --  m_maxResponseTime_ms = ndComponent.attribute("MaxResponseTime_ms").as_uint(m_maxResponseTime_ms);
      --  if(m_maxResponseTime_ms < 10) m_maxResponseTime_ms = 10;
      This.Max_Response_Time := UInt32_Attribute (XML_Node, "MaxResponseTime_ms", Default => This.Max_Response_Time);
      This.Max_Response_Time := UInt32'Max (This.Max_Response_Time, 10);

      --  // translate regular, impact, and task automation requests to unique automation requests
      --  addSubscriptionAddress(afrl::cmasi::AutomationRequest::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.AutomationRequest.Subscription, Unused);
      --  addSubscriptionAddress(afrl::impact::ImpactAutomationRequest::Subscription);
      This.Add_Subscription_Address (AFRL.Impact.ImpactAutomationRequest.Subscription, Unused);
      --  addSubscriptionAddress(uxas::messages::task::TaskAutomationRequest::Subscription);
      This.Add_Subscription_Address (UxAS.Messages.Lmcptask.TaskAutomationRequest.Subscription, Unused);

      --  // respond with appropriate automation response based on unique response
      --  addSubscriptionAddress(uxas::messages::task::UniqueAutomationResponse::Subscription);
      This.Add_Subscription_Address (UxAS.Messages.Lmcptask.UniqueAutomationResponse.Subscription, Unused);

      --  // track all entity configurations
      --  addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.EntityConfiguration.Subscription, Unused);
      --  std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
      --  for(auto child : childconfigs)
      --      addSubscriptionAddress(child);
      for Descendant of EntityConfiguration_Descendants loop
         This.Add_Subscription_Address (Descendant, Unused);
      end loop;

      --  // track all entity states
      --  addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.EntityState.Subscription, Unused);
      --  std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
      --  for(auto child : childstates)
      --      addSubscriptionAddress(child);
      for Descendant of EntityState_Descendants loop
         This.Add_Subscription_Address (Descendant, Unused);
      end loop;

      --  // track airspace constraints
      --  addSubscriptionAddress(afrl::cmasi::OperatingRegion::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.OperatingRegion.Subscription, Unused);
      --  addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.KeepInZone.Subscription, Unused);
      --  addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.KeepOutZone.Subscription, Unused);

      --  // track indicated locations of interest
      --  addSubscriptionAddress(afrl::impact::AreaOfInterest::Subscription);
      This.Add_Subscription_Address (AFRL.Impact.AreaOfInterest.Subscription, Unused);
      --  addSubscriptionAddress(afrl::impact::LineOfInterest::Subscription);
      This.Add_Subscription_Address (AFRL.Impact.LineOfInterest.Subscription, Unused);
      --  addSubscriptionAddress(afrl::impact::PointOfInterest::Subscription);
      This.Add_Subscription_Address (AFRL.Impact.PointOfInterest.Subscription, Unused);

      --  // track all tasks
      --  addSubscriptionAddress(afrl::cmasi::Task::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.LmcpTask.Subscription, Unused);
      --  std::vector< std::string > childtasks = afrl::cmasi::TaskDescendants();
      --  for(auto child : childtasks)
      --      addSubscriptionAddress(child);
      for Descendant of Lmcptask_Descendants loop
         This.Add_Subscription_Address (Descendant, Unused);
      end loop;

      --  // task removal and initialization
      --  addSubscriptionAddress(afrl::cmasi::RemoveTasks::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.RemoveTasks.Subscription, Unused);
      --  addSubscriptionAddress(uxas::messages::task::TaskInitialized::Subscription);
      This.Add_Subscription_Address (UxAS.Messages.Lmcptask.TaskInitialized.Subscription, Unused);

      --  // track errors during automation request pipeline
      --  addSubscriptionAddress(afrl::cmasi::ServiceStatus::Subscription);
      This.Add_Subscription_Address (AFRL.CMASI.ServiceStatus.Subscription, Unused);

      --  return true;
      Result := True;
   end Configure;

   ----------------
   -- Initialize --
   ----------------

   overriding
   procedure Initialize
     (This   : in out Automation_Request_Validator_Service;
      Result : out Boolean)
   is
      pragma Unreferenced (This); -- since not doing the Timers
   begin
      --  the C++ version creates the timers here (but we don't, unless we implement the timers).
      Result := True;
   end Initialize;

   -------------------------------
   -- Is_Any_Automation_Request --
   -------------------------------

   function Is_Any_Automation_Request (Msg : Object_Any) return Boolean is
      --  else if (afrl::cmasi::isAutomationRequest(receivedLmcpMessage->m_object) ||
      --          afrl::impact::isImpactAutomationRequest(receivedLmcpMessage->m_object) ||
      --          uxas::messages::task::isTaskAutomationRequest(receivedLmcpMessage->m_object))
      (Msg.all in AutomationRequest'Class       or
       Msg.all in ImpactAutomationRequest'Class or
       Msg.all in TaskAutomationRequest'Class);

   -----------------------------------
   -- Process_Received_LMCP_Message --
   -----------------------------------

   overriding
   procedure Process_Received_LMCP_Message
     (This             : in out Automation_Request_Validator_Service;
      Received_Message : not null Any_LMCP_Message;
      Should_Terminate : out Boolean)
   is
   begin
      if Received_Message.Payload.all in EntityConfiguration'Class then
         This.Handle_EntityConfig_Msg (EntityConfiguration_Any (Received_Message.Payload));

      elsif Received_Message.Payload.all in EntityState'Class then
         This.Handle_StateEntity_Msg (EntityState_Any (Received_Message.Payload));

      elsif Received_Message.Payload.all in LmcpTask'Class then
         This.Handle_InitializedTasks_Msg (LmcpTask_Any (Received_Message.Payload));

      elsif Received_Message.Payload.all in ServiceStatus'Class then
         This.Handle_ServiceStatus_Msg (Received_Message);

      elsif Received_Message.Payload.all in RemoveTasks'Class then
         This.Handle_RemoveTasks_Msg (Received_Message);

      elsif Received_Message.Payload.all in TaskInitialized'Class then
         This.Handle_TaskInitialized_Msg (Received_Message);

      elsif Received_Message.Payload.all in AreaOfInterest'Class then
         This.Handle_AreaOfInterest_Msg (Received_Message);

      elsif Received_Message.Payload.all in LineOfInterest'Class then
         This.Handle_LineOfInterest_Msg (Received_Message);

      elsif Received_Message.Payload.all in PointofInterest'Class then
         This.Handle_PointofInterest_Msg (Received_Message);

      elsif Received_Message.Payload.all in KeepInZone'Class then
         This.Handle_KeepInZone_Msg (Received_Message);

      elsif Received_Message.Payload.all in KeepOutZone'Class then
         This.Handle_KeepOutZone_Msg (Received_Message);

      elsif Received_Message.Payload.all in OperatingRegion'Class then
         This.Handle_OperatingRegion_Msg (Received_Message);

      elsif Is_Any_Automation_Request (Received_Message.Payload) then
         This.Handle_Automation_Request (Received_Message.Payload);

      elsif Received_Message.Payload.all in UniqueAutomationResponse'Class then
         This.Handle_Automation_Response (Received_Message.Payload);
      end if;

      --  Note the C++ code never returns anything other than False...
      Should_Terminate := False;
   end Process_Received_LMCP_Message;

   -----------------------------
   -- Handle_EntityConfig_Msg --
   -----------------------------

   procedure Handle_EntityConfig_Msg
     (This         : in out Automation_Request_Validator_Service;
      EntityConfig : EntityConfiguration_Any)
   is
      use Int64_Sets;
   begin
      --  m_availableConfigurationEntityIds.insert(entityConfig->getID());
      Include (This.Configs.Available_Configuration_Entity_Ids, EntityConfig.GetID);
   end Handle_EntityConfig_Msg;

   ----------------------------
   -- Handle_StateEntity_Msg --
   ----------------------------

   procedure Handle_StateEntity_Msg
     (This  : in out Automation_Request_Validator_Service;
      State : EntityState_Any)
   is
      use Int64_Sets;
   begin
      --  m_availableStateEntityIds.insert(entityState->getID());
      Include (This.Configs.Available_State_Entity_Ids, State.GetID);
   end Handle_StateEntity_Msg;

   ---------------------------------
   -- Handle_InitializedTasks_Msg --
   ---------------------------------

   procedure Handle_InitializedTasks_Msg
     (This : in out Automation_Request_Validator_Service;
      Job  : LmcpTask_Any)
   is
      use Int64_Sets;
   begin
      --  m_availableInitializedTasks.erase(task->getTaskID());
      Exclude (This.Configs.Available_Initialized_Tasks, Job.GetTaskID);
      --  m_availableTasks[task->getTaskID()] = task;
      declare
         Inserted : Boolean;
         C        : Int64_CMASI_Task_Maps.Cursor;
         use AFRL.Cmasi.LmcpTask.SPARK_Boundary;
         Wrapped_Job : constant Task_Kind_And_Id := Get_Kind_And_Id (Job);
      begin
         Int64_CMASI_Task_Maps.Insert
           (This.Configs.Available_Tasks,
            Key      =>  Job.GetTaskID,
            New_Item => Wrapped_Job,
            Position => C,
            Inserted => Inserted);
         if not Inserted then
            Int64_CMASI_Task_Maps.Replace_Element (This.Configs.Available_Tasks, C, Wrapped_Job);
         end if;
      end;
   end Handle_InitializedTasks_Msg;

   ------------------------------
   -- Handle_ServiceStatus_Msg --
   ------------------------------

   procedure Handle_ServiceStatus_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message)
   is
      --  log any error messages in the assignment pipeline
      --  auto sstatus = std::static_pointer_cast<afrl::cmasi::ServiceStatus>(receivedLmcpMessage->m_object);
      SStatus : constant ServiceStatus_Any := ServiceStatus_Any (Msg.Payload);
      use AFRL.CMASI.Enumerations;
      Clone   : KeyValuePair_Acc;
   begin
      --  if(sstatus->getStatusType() == afrl::cmasi::ServiceStatusType::Error)
      if SStatus.GetStatusType = Error then
         --  for(auto kvp : sstatus->getInfo())
         for KVP of SStatus.GetInfo.all loop
            --  m_errorResponse->getOriginalResponse()->getInfo().push_back(kvp->clone());
            Clone := new KeyValuePair'(KVP.all);
            afrl.cmasi.AutomationResponse.Vect_KeyValuePair_Acc.Append (This.Error_Response.GetOriginalResponse.GetInfo.all, Clone);
         end loop;
      end if;
   end Handle_ServiceStatus_Msg;

   ----------------------------
   -- Handle_RemoveTasks_Msg --
   ----------------------------

   procedure Handle_RemoveTasks_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message)
   is
      --  auto removeTasks = std::static_pointer_cast<afrl::cmasi::RemoveTasks>(receivedLmcpMessage->m_object);
      Remove : constant RemoveTasks_Any := RemoveTasks_Any (Msg.Payload);
      C      : Int64_CMASI_Task_Maps.Cursor;
      use Int64_Sets;
   begin
      --  for (auto& taskId : removeTasks->getTaskList())
      for Id of Remove.GetTaskList.all loop
         --  m_availableTasks.erase(taskId);
         C := Int64_CMASI_Task_Maps.Find (This.Configs.Available_Tasks, Key => Id);
         if Int64_CMASI_Task_Maps.Has_Element (This.Configs.Available_Tasks, C) then
            Int64_CMASI_Task_Maps.Delete (This.Configs.Available_Tasks, C);
         end if;

         --  m_availableInitializedTasks.erase(taskId);
         Exclude (This.Configs.Available_Initialized_Tasks, Id);
      end loop;
   end Handle_RemoveTasks_Msg;

   --------------------------------
   -- Handle_TaskInitialized_Msg --
   --------------------------------

   procedure Handle_TaskInitialized_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message)
   is
      --  auto taskInitialized = std::static_pointer_cast<uxas::messages::task::TaskInitialized>(receivedLmcpMessage->m_object);
      TaskInit : constant TaskInitialized_Any := TaskInitialized_Any (Msg.Payload);
      use Int64_Sets;
   begin
      --  m_availableInitializedTasks.insert(taskInitialized->getTaskID());
      Include (This.Configs.Available_Initialized_Tasks, TaskInit.GetTaskID);

      --  checkTasksInitialized();
      SPARK.Check_Tasks_Initialized (This);
   end Handle_TaskInitialized_Msg;

   -------------------------------
   -- Handle_AreaOfInterest_Msg --
   -------------------------------

   procedure Handle_AreaOfInterest_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message)
   is
      --  auto areaOfInterest = std::static_pointer_cast<afrl::impact::AreaOfInterest>(receivedLmcpMessage->m_object);
      Area : constant AreaOfInterest_Any := AreaOfInterest_Any (Msg.Payload);
      use Int64_Sets;
   begin
      --  m_availableAreaOfInterestIds.insert(areaOfInterest->getAreaID());
      Include (This.Configs.Available_Area_Of_Interest_Ids, Area.GetAreaID);
   end Handle_AreaOfInterest_Msg;

   -------------------------------
   -- Handle_LineOfInterest_Msg --
   -------------------------------

   procedure Handle_LineOfInterest_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message)
   is
      --  auto lineOfInterest = std::static_pointer_cast<afrl::impact::LineOfInterest>(receivedLmcpMessage->m_object);
      Line : constant LineOfInterest_Any := LineOfInterest_Any (Msg.Payload);
      use Int64_Sets;
   begin
      --  m_availableLineOfInterestIds.insert(lineOfInterest->getLineID());
      Include (This.Configs.Available_Line_Of_Interest_Ids, Line.GetLineID);
   end Handle_LineOfInterest_Msg;

   --------------------------------
   -- Handle_PointofInterest_Msg --
   --------------------------------

   procedure Handle_PointofInterest_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message)
   is
      --  auto pointOfInterest = std::static_pointer_cast<afrl::impact::PointOfInterest>(receivedLmcpMessage->m_object);
      Point : constant PointofInterest_Any := PointofInterest_Any (Msg.Payload);
      use Int64_Sets;
   begin
      --  m_availablePointOfInterestIds.insert(pointOfInterest->getPointID());
      Include (This.Configs.Available_Point_Of_Interest_Ids, Point.GetPointID);
   end Handle_PointofInterest_Msg;

   ---------------------------
   -- Handle_KeepInZone_Msg --
   ---------------------------

   procedure Handle_KeepInZone_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message)
   is
      --  auto keepInZone = std::static_pointer_cast<afrl::cmasi::KeepInZone>(receivedLmcpMessage->m_object);
      Zone : constant KeepInZone_Any := KeepInZone_Any (Msg.Payload);
      use Int64_Sets;
   begin
      --  m_availableKeepInZoneIds.insert(keepInZone->getZoneID());
      Include (This.Configs.Available_KeepIn_Zones_Ids, Zone.GetZoneID);
   end Handle_KeepInZone_Msg;

   ----------------------------
   -- Handle_KeepOutZone_Msg --
   ----------------------------

   procedure Handle_KeepOutZone_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message)
   is
      --  auto keepOutZone = std::static_pointer_cast<afrl::cmasi::KeepOutZone>(receivedLmcpMessage->m_object);
      Zone : constant KeepOutZone_Any := KeepOutZone_Any (Msg.Payload);
      use Int64_Sets;
   begin
      --  m_availableKeepOutZoneIds.insert(keepOutZone->getZoneID());
      Include (This.Configs.Available_KeepOut_Zones_Ids, Zone.GetZoneID);
   end Handle_KeepOutZone_Msg;

   --------------------------------
   -- Handle_OperatingRegion_Msg --
   --------------------------------

   procedure Handle_OperatingRegion_Msg
     (This : in out Automation_Request_Validator_Service;
      Msg  : Any_LMCP_Message)
   is
      --  auto operatingRegion = std::static_pointer_cast<afrl::cmasi::OperatingRegion>(receivedLmcpMessage->m_object);
      Region         : constant OperatingRegion_Any := OperatingRegion_Any (Msg.Payload);
      C              : Int64_Operating_Region_Maps.Cursor;
      Inserted       : Boolean;
      Wrapped_Region : constant OperatingRegionAreas := Get_Areas (OperatingRegion (Region.all));
   begin
      --  m_availableOperatingRegions[operatingRegion->getID()] = operatingRegion;
      Int64_Operating_Region_Maps.Insert
        (This.Configs.Available_Operating_Regions,
         Key       => Region.GetID,
         New_Item  => Wrapped_Region,
         Position  => C,
         Inserted  => Inserted);
      if not Inserted then
         Int64_Operating_Region_Maps.Replace_Element (This.Configs.Available_Operating_Regions, C, Wrapped_Region);
      end if;
   end Handle_OperatingRegion_Msg;

   -------------------------------
   -- Handle_Automation_Request --
   -------------------------------

   procedure Handle_Automation_Request
     (This    : in out Automation_Request_Validator_Service;
      Request : Object_Any)
   is
   begin
      SPARK.Handle_Automation_Request (This, Auto_Request => Wrap (Request));
   end Handle_Automation_Request;

   --------------------------------
   -- Handle_Automation_Response --
   --------------------------------

   procedure Handle_Automation_Response
     (This     : in out Automation_Request_Validator_Service;
      Response : Object_Any)
   is
      --  auto resp = std::static_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(autoResponse);
      Resp    : constant UniqueAutomationResponse_Acc := UniqueAutomationResponse_Acc (Response);
      Resp_Id : Int64;

      use UniqueAutomationRequest_Lists;
   begin
      --  if(m_pendingRequests.empty()) return;
       if Is_Empty (This.Pending_Requests) then
         return;
      end if;

      Resp_Id := Resp.GetResponseID;
      --  if (m_pendingRequests.front()->getRequestID() == resp->getResponseID() &&
      --      m_sandboxMap.find(resp->getResponseID()) != m_sandboxMap.end())
      if GetRequestId (First_Element (This.Pending_Requests).Content) = Resp_Id  and
         Int64_Request_Details_Maps.Contains (This.Sandbox, Resp_Id)
      then
         --  SendResponse(resp);
         This.Send_Response (Resp);
         --  m_sandboxMap.erase(resp->getResponseID());
         Int64_Request_Details_Maps.Delete (This.Sandbox, Resp_Id);
         --  m_pendingRequests.pop_front();
         Delete_First (This.Pending_Requests);
         --  sendNextRequest();
         This.Send_Next_Request;
      end if;
   end Handle_Automation_Response;

   -------------------
   -- Send_Response --
   -------------------

   procedure Send_Response
     (This : in out Automation_Request_Validator_Service;
      Resp : UniqueAutomationResponse_Acc)
   is
      Request : Request_Details;
      use Int64_Request_Details_Maps;
      C : Cursor;
   begin
      C := Find (This.Sandbox, Key => Resp.getResponseID);

      --  if(m_sandboxMap.find(resp->getResponseID()) == m_sandboxMap.end())
      if C = No_Element then
         --  can't find a corresponding type, so just send out a normal one
         declare
            --  auto cleanResponse = std::shared_ptr<afrl::cmasi::AutomationResponse>(resp->getOriginalResponse()->clone());
            CleanResponse : constant Object_Any := new AutomationResponse'(Resp.GetOriginalResponse.all);
         begin
            --  sendSharedLmcpObjectBroadcastMessage(cleanResponse);
            This.Send_Shared_LMCP_Object_Broadcast_Message (CleanResponse);
            --  return;
            return;
         end;
      end if;

      --  Ada: we know C designates an element so get it once, here, instead of serveral times below
      Request := Element (This.Sandbox, C);

      --  if (m_sandboxMap[resp->getResponseID()].requestType == TASK_AUTOMATION_REQUEST)
      if Request.RequestType = Task_Automation_Request then
         declare
            --  auto taskResponse = std::make_shared<uxas::messages::task::TaskAutomationResponse>();
            TaskResponse : constant TaskAutomationResponse_Acc := new TaskAutomationResponse;
         begin
            --  taskResponse->setOriginalResponse(resp->getOriginalResponse()->clone());
            TaskResponse.setOriginalResponse (new AutomationResponse'(Resp.getOriginalResponse.all));
            --  taskResponse->setResponseID(m_sandboxMap[resp->getResponseID()].taskRequestId);
            TaskResponse.setResponseId (Request.Task_Request_Id);

            --  add FinalStates to task responses
            --  for(auto st : resp->getFinalStates())
            for St of Resp.getFinalStates.all loop
               --  taskResponse->getFinalStates().push_back(st->clone());
               uxas.messages.lmcptask.TaskAutomationResponse.Vect_PlanningState_Acc.Append (TaskResponse.getFinalStates.all, new PlanningState'(St.all));
            end loop;
            --  sendSharedLmcpObjectBroadcastMessage(taskResponse);
            This.Send_Shared_LMCP_Object_Broadcast_Message (Object_Any (TaskResponse));
         end;

      --  else if (m_sandboxMap[resp->getResponseID()].requestType == AUTOMATION_REQUEST)
      elsif Request.RequestType = Automation_Request then
         declare
            --  auto cleanResponse = std::shared_ptr<afrl::cmasi::AutomationResponse>(resp->getOriginalResponse()->clone());
            CleanResponse : constant Object_Any := new AutomationResponse'(Resp.GetOriginalResponse.all);
         begin
            --  sendSharedLmcpObjectBroadcastMessage(cleanResponse);
            This.Send_Shared_LMCP_Object_Broadcast_Message (CleanResponse);
         end;

      else
         --  look up play and solution IDs
         declare
            --  auto sandResponse = std::shared_ptr<afrl::impact::ImpactAutomationResponse> (new afrl::impact::ImpactAutomationResponse);
            SandResponse : constant ImpactAutomationResponse_Acc := new ImpactAutomationResponse;
         begin
            --  sandResponse->setPlayID(m_sandboxMap[resp->getResponseID()].playId);
            SandResponse.setPlayID (Request.Play_Id);
            --  sandResponse->setSolutionID(m_sandboxMap[resp->getResponseID()].solnId);
            SandResponse.setSolutionID (Request.Soln_Id);
            --  sandResponse->setTrialResponse(resp->getOriginalResponse()->clone());
            SandResponse.setTrialResponse (new AutomationResponse'(Resp.GetOriginalResponse.all));
            --  sandResponse->setSandbox(true);
            SandResponse.setSandbox (True);

            --  sendSharedLmcpObjectBroadcastMessage(sandResponse);
            This.Send_Shared_LMCP_Object_Broadcast_Message (Object_Any (SandResponse));
         end;
      end if;
   end Send_Response;

   -----------------------
   -- Send_Next_Request --
   -----------------------

   procedure Send_Next_Request
     (This : in out Automation_Request_Validator_Service)
   is
      Request : UniqueAutomationRequest_Acc;
      use UniqueAutomationRequest_Lists;
   begin
      if Is_Empty (This.Pending_Requests) then
      --      // no other requests in queue, disable timer
      --      uxas::common::TimerManager::getInstance().disableTimer(m_responseTimerId,0);
      --      return;
         return;
      end if;

      --  // retrieve next request to send out
      --  auto uniqueAutomationRequest = m_pendingRequests.front();
      Request := new UniqueAutomationRequest'(Unwrap (First_Element (This.Pending_Requests).Content));

      --  // sending a new request, so clear out the old errors
      --  m_errorResponse->setOriginalResponse(new afrl::cmasi::AutomationResponse);
      This.Error_Response.setOriginalResponse (new AutomationResponse);
      --  m_errorResponse->setResponseID(uniqueAutomationRequest->getRequestID());
      This.Error_Response.setResponseID (Request.getRequestID);

      --  // send next request
      --  sendSharedLmcpObjectBroadcastMessage(uniqueAutomationRequest);
      This.Send_Shared_LMCP_Object_Broadcast_Message (Object_Any (Request));

      --  // report start of assignment pipeline
      declare
         Service : ServiceStatus_Acc;
         KVP     : KeyValuePair_Acc;
         use Ada.Strings.Unbounded;
         Message : Unbounded_String;
      begin
         --  auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
         Service := new ServiceStatus;
         --  serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
         Service.SetStatusType (AFRL.CMASI.Enumerations.Information);

         --  auto keyValuePair = new afrl::cmasi::KeyValuePair;
         KVP := new KeyValuePair;
         --  std::string message = "UniqueAutomationRequest[" + std::to_string(uniqueAutomationRequest->getRequestID()) + "] - sent";
         Message := To_Unbounded_String ("UniqueAutomationRequest[" & String_Utils.To_String (Request.getRequestID) & "] - sent");
         --  keyValuePair->setKey(message);
         KVP.setKey (Message);
         --  serviceStatus->getInfo().push_back(keyValuePair);
         AFRL.CMASI.ServiceStatus.Vect_KeyValuePair_Acc.Append (Service.getInfo.all, KVP);
         --  keyValuePair = nullptr;
         --  sendSharedLmcpObjectBroadcastMessage(serviceStatus);
         This.Send_Shared_LMCP_Object_Broadcast_Message (Object_Any (Service));
      end;

      --  // reset the timer
      --  uxas::common::TimerManager::getInstance().startSingleShotTimer(m_responseTimerId, m_maxResponseTime_ms);
   end Send_Next_Request;

   ----------------------
   -- UInt32_Attribute --
   ----------------------

   function UInt32_Attribute
     (XML_Node : DOM.Core.Element;
      Name     : String;
      Default  : UInt32)
   return UInt32
   is
      use DOM.Core;
      Attr_Value : constant DOM_String := Elements.Get_Attribute (XML_Node, Name);
   begin
      if Attr_Value /= "" and then (for all C of Attr_Value => C in '0' .. '9')
      then
         return UInt32'Value (Attr_Value);
      else
         return Default;
      end if;
   end UInt32_Attribute;

   -----------------------------
   -- Package Executable Part --
   -----------------------------

   --  This is the executable part for the package, invoked automatically and only once.
begin
   --  All concrete service subclasses must call this procedure in their
   --  own package like this, with their own params. The effect is the same as the
   --  following:
   --
   --    AutomationRequestValidatorService::ServiceBase::CreationRegistrar<AutomationRequestValidatorService>
   --    AutomationRequestValidatorService::s_registrar(AutomationRequestValidatorService::s_registryServiceTypeNames());
   --
   --  located at the top of the cpp file

   Register_Service_Creation_Function_Pointers (Registry_Service_Type_Names, Create'Access);
end UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation;


with Bounded_Dynamic_Strings;
with afrl.cmasi.KeyValuePair;       use afrl.cmasi.KeyValuePair;
with Ada.Strings.Unbounded;
with afrl.cmasi.AutomationResponse; use afrl.cmasi.AutomationResponse;

package body UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation.SPARK with SPARK_Mode is

   function Prove_Same_Requests_Valid
     (This : Configuration_Data;
      R, S : My_UniqueAutomationRequest) return Boolean
   is (Valid_Automation_Request (This, S))
   with
     Ghost,
     Global => null,
     Pre    => Same_Requests (R, S) and then Valid_Automation_Request (This, R),
     Post   => Prove_Same_Requests_Valid'Result;

   procedure Prove_Validity_Preserved
     (Data1, Data2 : Configuration_Data;
      R : My_UniqueAutomationRequest)
   with
     Ghost,
     Global => null,
     Pre    => Data1 = Data2,
     Post   => Valid_Automation_Request (Data1, R) = Valid_Automation_Request (Data2, R);

   procedure Prove_Validity_Preserved
     (Data1, Data2 : Configuration_Data;
      R_Queue : UniqueAutomationRequest_Lists.Formal_Model.M.Sequence)
   with
     Ghost,
     Global => null,
     Pre    => Data1 = Data2,
     Post   => (for all R of R_Queue => Valid_Automation_Request (Data1, R.Content) = Valid_Automation_Request (Data2, R.Content));

   procedure Prove_Validity_Preserved
     (Data               : Configuration_Data;
      R_Queue1, R_Queue2 : UniqueAutomationRequest_Lists.Formal_Model.M.Sequence)
   with
     Ghost,
     Global => null,
     Pre    => Same_Requests (R_Queue1, R_Queue2),
     Post   =>
       (for all I in 1 .. UniqueAutomationRequest_Lists.Formal_Model.M.Length (R_Queue1) =>
              Valid_Automation_Request (Data,
            UniqueAutomationRequest_Lists.Formal_Model.Element (R_Queue1, I).Content) =
              Valid_Automation_Request (Data,
            UniqueAutomationRequest_Lists.Formal_Model.Element (R_Queue2, I).Content));

   procedure Prove_Validity_Preserved
     (Data1, Data2 : Configuration_Data;
      R : My_UniqueAutomationRequest) is null;

   procedure Prove_Validity_Preserved
     (Data1, Data2 : Configuration_Data;
      R_Queue      : UniqueAutomationRequest_Lists.Formal_Model.M.Sequence)
   is
      use UniqueAutomationRequest_Lists.Formal_Model;
   begin
      for I in 1 .. M.Length (R_Queue) loop
         Prove_Validity_Preserved (Data1, Data2, M.Get (R_Queue, I).Content);
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              Valid_Automation_Request (Data1, M.Get (R_Queue, J).Content) = Valid_Automation_Request (Data2, M.Get (R_Queue, J).Content));
      end loop;
   end Prove_Validity_Preserved;

   procedure Prove_Validity_Preserved
     (Data               : Configuration_Data;
      R_Queue1, R_Queue2 : UniqueAutomationRequest_Lists.Formal_Model.M.Sequence) is null;

   procedure Send_Next_Request_Wrapper (This : in out Automation_Request_Validator_Service) with
     Post => This.Configs'Old = This.Configs
     and Same_Requests
       (UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks),
        UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks)'Old)
       and Same_Requests
         (UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests),
          UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests)'Old);
   --  Wrapper to add a contract to Send_Next_Request

   procedure Send_Next_Request_Wrapper (This : in out Automation_Request_Validator_Service) with
     SPARK_Mode => Off
   is
   begin
      This.Send_Next_Request;
   end Send_Next_Request_Wrapper;

   -----------------------------
   -- Check_Tasks_Initialized --
   -----------------------------

   procedure Check_Tasks_Initialized
     (This : in out Automation_Request_Validator_Service)
   is
      -- checks to ensure all tasks are initialized for the requests in the 'task wait' queue
      -- if so, moves them to the 'pending' queue, otherwise sets a timer to wait

      AreAllTasksReady       : Boolean := True;
      IsNewPendingRequest    : Boolean := False;
      All_Requests_Valid_Old : constant Boolean := All_Requests_Valid (This) with Ghost;

   begin
      while AreAllTasksReady
        and then not UniqueAutomationRequest_Lists.Is_Empty
          (This.Requests_Waiting_For_Tasks)
      loop
         pragma Loop_Invariant
           (if All_Requests_Valid (This)'Loop_Entry then All_Requests_Valid (This));
         declare
            use Int64_Vects;
            use UniqueAutomationRequest_Lists;
            TaskIds : constant Int64_Vect := Get_TaskList_From_OriginalRequest
              (First_Element (This.Requests_Waiting_For_Tasks).Content);
            Request_Q_Tmp : UniqueAutomationRequest_Ref_Deque with Ghost;
            use UniqueAutomationRequest_Lists.Formal_Model;
         begin
            for I in First_Index (TaskIds) .. Last_Index (TaskIds) loop
               declare
                  use Int64_Sets;
                  TaskId          : constant Int64 := Element (TaskIds, I);
                  ItStartedTaskId : constant Boolean :=
                    Contains (This.Configs.Available_Initialized_Tasks, taskId);
               begin
                  if not itStartedTaskId then
                     AreAllTasksReady := False;
                     exit;
                  end if;
               end;
            end loop;

            if AreAllTasksReady then
               -- move from 'task wait' queue
               IsNewPendingRequest := True;
               pragma Assert
                 (if  All_Requests_Valid_Old then
                     Prove_Same_Requests_Valid
                    (This.Configs,
                     M.Get (Model (This.Requests_Waiting_For_Tasks), 1).Content,
                     First_Element (This.Requests_Waiting_For_Tasks).Content));
               Request_Q_Tmp := This.Pending_Requests;
               Append (This.Pending_Requests, First_Element (This.Requests_Waiting_For_Tasks));
               pragma Assert (if All_Requests_Valid_Old then (for all I in 1 .. Length (Request_Q_Tmp) =>
                                  Prove_Same_Requests_Valid (This.Configs,
                                  M.Get (Model (Request_Q_Tmp), I).Content,
                                  M.Get (Model (This.Pending_Requests), I).Content)));
               pragma Assert
                 (if All_Requests_Valid_Old then
                     Prove_Same_Requests_Valid (This.Configs, First_Element (This.Requests_Waiting_For_Tasks).Content,
                    M.Get (Model (This.Pending_Requests), Length (This.Pending_Requests)).Content));
               pragma Assert (if All_Requests_Valid_Old then All_Requests_Valid (This));
               Request_Q_Tmp := This.Requests_Waiting_For_Tasks;
               Delete_First (This.Requests_Waiting_For_Tasks);
               pragma Assert
                 (if All_Requests_Valid_Old then
                    (for all I in 1 .. Length (This.Requests_Waiting_For_Tasks) =>
                         Prove_Same_Requests_Valid
                       (This.Configs,
                        M.Get (Model (Request_Q_Tmp), I + 1).Content,
                        M.Get (Model (This.Requests_Waiting_For_Tasks), I).Content)));

               --  re-set the task initialized check timer
               --  [Claire] ToDo : I could not find TimerManager
               --  uxas.Common.TimerManager::getInstance().startSingleShotTimer(m_taskInitTimerId, m_maxResponseTime_ms);
               pragma Compile_time_Warning (Standard.True, "Check_Tasks_Initialized is incomplete");
            end if;
         end;
      end loop;
      pragma Assert
        (if All_Requests_Valid_Old then All_Requests_Valid (This));

      --  [Claire] ToDo : I could not find TimerManager
      --      if(isNewPendingRequest)
      if IsNewPendingRequest then
      --      {
      --          // if timer not started (i.e. not currently waiting for a response),
      --          // then send the one that just got added
      --          if(!uxas::common::TimerManager::getInstance().isTimerActive(m_responseTimerId))
      --          {
      --              sendNextRequest();
         declare
            Old_Confs : constant Configuration_Data := This.Configs with Ghost;
            Old_Pending_Request : constant UniqueAutomationRequest_Lists.Formal_Model.M.Sequence :=
              UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests) with Ghost;
            Old_Waiting_Request : constant UniqueAutomationRequest_Lists.Formal_Model.M.Sequence :=
              UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks) with Ghost;
         begin
            Send_Next_Request_Wrapper (This);
            Prove_Validity_Preserved (Old_Confs, Old_Waiting_Request, UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks));
            Prove_Validity_Preserved (Old_Confs, Old_Pending_Request, UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests));
            Prove_Validity_Preserved (Old_Confs, This.Configs, UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks));
            Prove_Validity_Preserved (Old_Confs, This.Configs, UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests));
            pragma Assert
              (if All_Requests_Valid_Old then All_Requests_Valid (This));
         end;
      --          }
      --      }
      --      else if(!uxas::common::TimerManager::getInstance().isTimerActive(m_taskInitTimerId) && !m_requestsWaitingForTasks.empty())
      --      {
      --          // top of task-init queue is still not ready, start timer if not already started
      --          uxas::common::TimerManager::getInstance().startSingleShotTimer(m_taskInitTimerId, m_maxResponseTime_ms);
      --      }
      end if;

      --      if(m_requestsWaitingForTasks.empty())
      --      {
      --          // all tasks have been initialized, so disable timer
      --          uxas::common::TimerManager::getInstance().disableTimer(m_taskInitTimerId, 0);
      --      }
   end Check_Tasks_Initialized;

   ------------------
   -- Empty_Vector --
   ------------------

   function Empty_Vector return Int64_Vect is
   begin
      pragma Warnings (Off);
      return V : Int64_Vect do
         null;
      end return;
      pragma Warnings (On);
   end Empty_Vector;

   -------------------------------
   -- Handle_Automation_Request --
   -------------------------------

   procedure Handle_Automation_Request
     (This         : in out Automation_Request_Validator_Service;
      Auto_Request : My_Object_Any)
   is
      Request             : Object'Class renames Deref (Auto_Request);
      UniqueAutomationReq : My_UniqueAutomationRequest;
      Id                  : Int64;
      All_Requests_Valid_Old : constant Boolean := All_Requests_Valid (This) with Ghost;

   begin

      pragma Assert (if All_Requests_Valid_Old then All_Requests_Valid (This));

      Get_Unique_Entity_Send_Message_Id (Id);
      setRequestID (UniqueAutomationReq, Id);

      pragma Assert (if All_Requests_Valid_Old then All_Requests_Valid (This));

      --  [Claire] Use membership test instead of IsImpactAutomationRequest

      if Request in ImpactAutomationRequest then
         declare
            Sand    : ImpactAutomationRequest renames ImpactAutomationRequest (Request);
            Details : constant Request_Details :=
              (RequestType     => Sandbox_Automation_Request,
               Play_Id         => Sand.getPlayID,
               Soln_Id         => Sand.getSolutionID,
               Task_Request_Id => <>);
         begin
            setRequestID (UniqueAutomationReq, Sand.getRequestID);
            Int64_Request_Details_Maps.Insert
              (This.Sandbox, getRequestID (uniqueAutomationReq), Details);
            Copy_OriginalRequest_From_ImpactAutomationRequest
              (Target => UniqueAutomationReq,
               Source => Sand);
         end;
         pragma Assert (if All_Requests_Valid_Old then All_Requests_Valid (This));
         pragma Assert
           (Is_Corresponding_UniqueRequest (uniqueAutomationReq, Request));

      --  [Claire] Use membership test instead of IsTaskAutomationRequest

      elsif Request in TaskAutomationRequest then
         declare
            TaskAutomationReq : TaskAutomationRequest renames TaskAutomationRequest (Request);
            Details : constant Request_Details :=
              (RequestType     => Task_Automation_Request,
               Task_Request_Id => TaskAutomationReq.getRequestID,
               others          => <>);
         begin
            setRequestID (UniqueAutomationReq, TaskAutomationReq.getRequestID);

            Copy_OriginalRequest_From_TaskAutomationRequest
              (Target => UniqueAutomationReq,
               Source => TaskAutomationReq);
            Copy_PlanningState_From_TaskAutomationRequest
              (Target => UniqueAutomationReq,
               Source => TaskAutomationReq);
            Int64_Request_Details_Maps.Insert
              (This.Sandbox, getRequestID (uniqueAutomationReq), Details);
         end;
         pragma Assert (if All_Requests_Valid_Old then All_Requests_Valid (This));
         pragma Assert
           (Is_Corresponding_UniqueRequest (uniqueAutomationReq, Request));
      else
         declare
            Details : constant Request_Details :=
              (RequestType => Automation_Request,
               others      => <>);
         begin
            Copy_OriginalRequest_From_AutomationRequest
              (Target => UniqueAutomationReq,
               Source => Auto_Request);
            Int64_Request_Details_Maps.Insert
              (This.Sandbox, getRequestID (uniqueAutomationReq), Details);
         end;

         pragma Assert (if All_Requests_Valid_Old then All_Requests_Valid (This));
         pragma Assert
           (Is_Corresponding_UniqueRequest (uniqueAutomationReq, Request));
      end if;

      declare
         IsReady       : Boolean;
         Request_Q_Tmp : UniqueAutomationRequest_Ref_Deque;
         use UniqueAutomationRequest_Lists;
         use UniqueAutomationRequest_Lists.Formal_Model;
      begin
         Check_Automation_Request_Requirements (This, UniqueAutomationReq, IsReady);
         pragma Assert (if All_Requests_Valid_Old then All_Requests_Valid (This));
         if IsReady then
            Request_Q_Tmp := This.Requests_Waiting_For_Tasks;
            Append
              (This.Requests_Waiting_For_Tasks, (Content => UniqueAutomationReq));
            pragma Assert (Valid_Automation_Request (This.Configs, UniqueAutomationReq));
            pragma Assert
              (if All_Requests_Valid_Old then
                 (for all I in 1 ..UniqueAutomationRequest_Lists.Length (Request_Q_Tmp) =>
                      Prove_Same_Requests_Valid
                       (This.Configs,
                        M.Get (Model (Request_Q_Tmp), I).Content,
                        M.Get (Model (This.Requests_Waiting_For_Tasks), I).Content)));
            pragma Assert
              (Prove_Same_Requests_Valid (This.Configs, UniqueAutomationReq,
               M.Get (Model (This.Requests_Waiting_For_Tasks), Length (This.Requests_Waiting_For_Tasks)).Content));
            Check_Tasks_Initialized (This);
         end if;
      end;

   end Handle_Automation_Request;

   ------------------------------------------
   -- IsCheckAutomationRequestRequirements --
   ------------------------------------------

   procedure Check_Automation_Request_Requirements
     (This    : in out Automation_Request_Validator_Service;
      Request : My_UniqueAutomationRequest;
      IsReady : out Boolean)
   is

      procedure Send_Error_Response
        (This             : in out Automation_Request_Validator_Service;
         Request          : My_UniqueAutomationRequest;
         ReasonForFailure : Bounded_Dynamic_Strings.Sequence;
         ErrResponseID    : out Int64)
        with Post => This.Configs'Old = This.Configs
        and Same_Requests
          (UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks),
           UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks)'Old)
          and Same_Requests
            (UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests),
             UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests)'Old);
      --  [Claire] Code factored out because of access types.

      -------------------------
      -- Send_Error_Response --
      -------------------------

      procedure Send_Error_Response
        (This             : in out Automation_Request_Validator_Service;
         Request          : My_UniqueAutomationRequest;
         ReasonForFailure : Bounded_Dynamic_Strings.Sequence;
         ErrResponseID    : out Int64)
      with SPARK_Mode => Off
      is
         KValuePair  : constant KeyValuePair_Acc := new KeyValuePair;
         ErrResponse : constant UniqueAutomationResponse_Acc :=
           new UniqueAutomationResponse;
      begin
         --  [Claire] ToDo : What is that?
         --          UXAS_LOG_WARN(reasonForFailure.str());
         KValuePair.setKey (Ada.Strings.Unbounded.To_Unbounded_String ("RequestValidator"));
         KValuePair.setValue (Ada.Strings.Unbounded.To_Unbounded_String (Bounded_Dynamic_Strings.Value (ReasonForFailure)));
         if ErrResponse.getOriginalResponse = null then
            ErrResponse.setOriginalResponse (new AutomationResponse);
         end if;
         ErrResponse.setResponseID (getRequestID (Request));
         afrl.cmasi.AutomationResponse.Vect_KeyValuePair_Acc.Append (ErrResponse.GetOriginalResponse.GetInfo.all, KValuePair);
         Send_Response(This, ErrResponse);
         ErrResponseID := ErrResponse.getResponseID;
      end Send_Error_Response;

      use Int64_Vects;
      use Bounded_Dynamic_Strings;
      ReasonForFailure : Sequence (100) :=
        Instance
          (100, String'("Automation Request ID["
           & Int64'Image (getRequestID (Request)) & "] Not Ready ::"));
      EntityIds        : constant Int64_Vect :=
        Get_EntityList_From_OriginalRequest (Request);

   begin
      IsReady := True;

      if not Is_Empty (EntityIds) then

         -- check for required entity configurations, if none are required, make sure there is at least one

         if not (Int64_Sets.Is_Empty (This.Configs.Available_Configuration_Entity_Ids)) then

            --  [Claire] Redundant check?

            if not Is_Empty (EntityIds) then
               for I in First_Index (EntityIds) .. Last_Index (EntityIds) loop
                  declare
                     use Int64_Sets;
                     Id : constant Int64 := Element (EntityIds, I);
                  begin
                     if not Contains (This.Configs.Available_Configuration_Entity_Ids, Id) then
                        Append (To   => ReasonForFailure,
                                Tail => String'("- EntityConfiguration for Entity Id["
                                  & Int64'Image (id) & "] not available."));
                        IsReady := False;
                     end if;

                     pragma Loop_Invariant
                       (IsReady
                        = (for all K in First_Index (EntityIds) .. I =>
                            Contains (This.Configs.Available_Configuration_Entity_Ids, Element (EntityIds, K))));
                  end;
               end loop;
            end if;
         else
            Append (To   => ReasonForFailure,
                    Tail => "- No EntityConfigurations available." );
            IsReady := False;
         end if;

         -- check for required entity states, if none are required, make sure there is at least one with matching configuration

         if not (Int64_Sets.Is_Empty (This.Configs.Available_State_Entity_Ids)) then
            for I in First_Index (EntityIds) .. Last_Index (EntityIds) loop
               pragma Loop_Invariant
                 (IsReady = (IsReady'Loop_Entry
                  and then ((for all K in First_Index (EntityIds) .. I - 1 =>
                      Int64_Sets.Contains (This.Configs.Available_State_Entity_Ids, Element (EntityIds, K))
                    or Contains (Get_PlanningStates_Ids (Request), Element (EntityIds, K))))));

               declare
                  use Int64_Sets;
                  Id           : constant Int64 := Element (EntityIds, I);
                  IsReadyLocal : Boolean := false;
               begin

                  if Contains (This.Configs.Available_State_Entity_Ids, Id) then
                     IsReadyLocal := true;
                  end if;

                  if not IsReadyLocal then
                     declare
                        planningStateIds : constant Int64_Vect :=
                          Get_PlanningStates_Ids (Request);
                     begin
                        for I in First_Index (planningStateIds) .. Last_Index (planningStateIds) loop
                           declare
                              planningStateId : constant Int64 := Element (planningStateIds, I);
                           begin
                              if planningStateId = Id then
                                 pragma Assert (Contains (Get_PlanningStates_Ids (Request), Id));
                                 IsReadyLocal := true;
                                 exit;
                              end if;
                           end;
                           pragma Loop_Invariant
                             (for all K in First_Index (planningStateIds) .. I =>
                                  Element (planningStateIds, K) /= Id);
                        end loop;
                     end;
                  end if;
                  pragma Assert
                    (IsReadyLocal =
                       (Contains (This.Configs.Available_State_Entity_Ids, Element (EntityIds, I))
                        or Contains (Get_PlanningStates_Ids (Request), Element (EntityIds, I))));

                  if not IsReadyLocal then
                     IsReady := False;
                     Append (To   => ReasonForFailure,
                             Tail => "- EntityState for Entity Id["
                             & Int64'Image (id) & "] not available.");
                  end if;
               end;
            end loop;
            pragma Assert
              (IsReady =
                 Check_For_Required_Entity_Configurations
                   (Entity_Ids      => EntityIds,
                    Configurations  => This.Configs.Available_Configuration_Entity_Ids,
                    States          => This.Configs.Available_State_Entity_Ids,
                    Planning_States => Get_PlanningStates_Ids (Request)));

         else
            Append (To   => ReasonForFailure,
                    Tail => "- No EntityStates available.");
            IsReady := False;
            pragma Assert
              (not (Int64_Sets.Contains
                 (This.Configs.Available_State_Entity_Ids, Int64_Vects.First_Element (EntityIds))));
            pragma Assert
              (not Check_For_Required_Entity_Configurations
                 (Entity_Ids      => EntityIds,
                  Configurations  => This.Configs.Available_Configuration_Entity_Ids,
                  States          => This.Configs.Available_State_Entity_Ids,
                  Planning_States => Get_PlanningStates_Ids (Request)));
         end if;
         pragma Assert
           (IsReady =
              Check_For_Required_Entity_Configurations
                (Entity_Ids      => EntityIds,
                 Configurations  => This.Configs.Available_Configuration_Entity_Ids,
                 States          => This.Configs.Available_State_Entity_Ids,
                 Planning_States => Get_PlanningStates_Ids (Request)));
      else --  if(!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())
         pragma Assert (Is_Empty (EntityIds));

         if not (Int64_Sets.Is_Empty (This.Configs.Available_Configuration_Entity_Ids))
           and then not Int64_Sets.Is_Empty (This.Configs.Available_State_Entity_Ids)
         then
            declare
               IsFoundAMatch : Boolean := False;
               use Int64_Sets;
               use Int64_Sets.Formal_Model;
               use all type P.Map;
               use all type E.Sequence;
            begin
               --  [Claire] Should one of the loops be on This.Available_State_Entity_Ids ?
               --  I assumed so and corrected the loop.
               for Id1 in This.Configs.Available_Configuration_Entity_Ids loop
                  pragma Loop_Invariant
                    (for all K in 1 .. Get (Positions (This.Configs.Available_Configuration_Entity_Ids), Id1) - 1 =>
                        not Contains (This.Configs.Available_State_Entity_Ids, Get (Elements (This.Configs.Available_Configuration_Entity_Ids), K)));
                  pragma Loop_Invariant (not IsFoundAMatch);
                  for Id2 in This.Configs.Available_State_Entity_Ids loop
                    if Element (This.Configs.Available_Configuration_Entity_Ids, Id1) = Element (This.Configs.Available_State_Entity_Ids, Id2) then
                        IsFoundAMatch := True;
                        exit;
                     end if;
                     pragma Loop_Invariant
                       (for all K in 1 .. Get (Positions (This.Configs.Available_State_Entity_Ids), Id2) =>
                          Element (This.Configs.Available_Configuration_Entity_Ids, Id1) /= Get (Elements (This.Configs.Available_State_Entity_Ids), K));
                     pragma Loop_Invariant (not IsFoundAMatch);
                  end loop;
                  if IsFoundAMatch then
                     exit;
                  end if;
               end loop;
               if not IsFoundAMatch then
                  Append (To   => ReasonForFailure,
                          Tail => "- No EntityStates that match EntityConfigurations"
                          & " are available.");
                  IsReady := False;
               end if;
            end;
        else
            if Int64_Sets.Is_Empty (This.Configs.Available_Configuration_Entity_Ids) then
                  Append (To   => ReasonForFailure,
                          Tail => "- No EntityConfigurations available." );
            else
                  Append (To   => ReasonForFailure,
                          Tail => "- No EntityStates available.");
            end if;
            IsReady := False;
         end if;
         pragma Assert
           (IsReady =
              Check_For_Required_Entity_Configurations
                (Entity_Ids      => EntityIds,
                 Configurations  => This.Configs.Available_Configuration_Entity_Ids,
                 States          => This.Configs.Available_State_Entity_Ids,
                 Planning_States => Get_PlanningStates_Ids (Request)));
      end if;
      pragma Assert_And_Cut
        (IsReady =
            Check_For_Required_Entity_Configurations
           (Entity_Ids      => EntityIds,
            Configurations  => This.Configs.Available_Configuration_Entity_Ids,
            States          => This.Configs.Available_State_Entity_Ids,
            Planning_States => Get_PlanningStates_Ids (Request)));

      -- check for required operating region and keepin/keepout zones

      if Get_OperatingRegion_From_OriginalRequest (Request) /= 0 then
         declare
            use all type Int64_Operating_Region_Maps.Cursor;
            Pos : constant Int64_Operating_Region_Maps.Cursor :=
              Find (This.Configs.Available_Operating_Regions,
                    Get_OperatingRegion_From_OriginalRequest (Request));
         begin
            if Pos /= Int64_Operating_Region_Maps.No_Element then
               pragma Assert (Contains (This.Configs.Available_Operating_Regions,
                    Get_OperatingRegion_From_OriginalRequest (Request)));
               declare
                  ItOperatingRegion : constant OperatingRegionAreas :=
                    Element (This.Configs.Available_Operating_Regions, Pos);
                  KeepInAreas       : constant Int64_Vect := ItOperatingRegion.KeepInAreas;
                  KeepOutAreas      : constant Int64_Vect := ItOperatingRegion.KeepOutAreas;
                  use Int64_Sets;
               begin
                  for I in First_Index (KeepInAreas) .. Last_Index (KeepInAreas) loop
                     declare
                        KeepInArea : constant Int64 := Element (KeepInAreas, I);
                     begin
                        if not Contains (This.Configs.Available_KeepIn_Zones_Ids, KeepInArea) then
                           Append (To   => ReasonForFailure,
                                   Tail => "- KeepInArea Id["
                                   & Int64'Image (keepInArea) & "] not available.");
                           IsReady := False;
                        end if;
                        pragma Loop_Invariant
                          (IsReady =
                             (IsReady'Loop_Entry and then
                             (for all K in First_Index (KeepInAreas) .. I =>
                                  Contains (This.Configs.Available_KeepIn_Zones_Ids, Element (KeepInAreas, K)))));
                     end;
                  end loop;
                  for I in First_Index (KeepOutAreas) .. Last_Index (KeepOutAreas) loop
                     declare
                        KeepOutArea : constant Int64 := Element (KeepOutAreas, I);
                     begin
                        if not Contains (This.Configs.Available_KeepOut_Zones_Ids, KeepOutArea) then
                           Append (To   => ReasonForFailure,
                                   Tail => "- KeepOutArea Id["
                                   & Int64'Image (keepOutArea) & "] not available.");
                           IsReady := False;
                        end if;
                        pragma Loop_Invariant
                          (IsReady =
                             (IsReady'Loop_Entry and then
                             (for all K in First_Index (KeepOutAreas) .. I =>
                                  Contains (This.Configs.Available_KeepOut_Zones_Ids, Element (KeepOutAreas, K)))));
                     end;
                  end loop;
               end;
               pragma Assert
                 (IsReady =
                    (Check_For_Required_Entity_Configurations
                         (Entity_Ids      => EntityIds,
                          Configurations  => This.Configs.Available_Configuration_Entity_Ids,
                          States          => This.Configs.Available_State_Entity_Ids,
                          Planning_States => Get_PlanningStates_Ids (Request))
                     and then
                     Check_For_Required_Operating_Region_And_Keepin_Keepout_Zones
                       (Operating_Region  => Get_OperatingRegion_From_OriginalRequest (Request),
                        Operating_Regions => This.Configs.Available_Operating_Regions,
                        KeepIn_Zones_Ids  => This.Configs.Available_KeepIn_Zones_Ids,
                        KeepOut_Zones_Ids => This.Configs.Available_KeepOut_Zones_Ids)));
            else
               Append (To   => ReasonForFailure,
                       Tail => "- OperatingRegion Id["
                       & Int64'Image (Get_OperatingRegion_From_OriginalRequest (Request))
                       & "] not available.");
               IsReady := False;
               pragma Assert
                 (not Check_For_Required_Operating_Region_And_Keepin_Keepout_Zones
                    (Operating_Region  => Get_OperatingRegion_From_OriginalRequest (Request),
                     Operating_Regions => This.Configs.Available_Operating_Regions,
                     KeepIn_Zones_Ids  => This.Configs.Available_KeepIn_Zones_Ids,
                     KeepOut_Zones_Ids => This.Configs.Available_KeepOut_Zones_Ids));
            end if;
         end;
      end if;

      pragma Assert_And_Cut
        (IsReady =
            (Check_For_Required_Entity_Configurations
           (Entity_Ids      => EntityIds,
            Configurations  => This.Configs.Available_Configuration_Entity_Ids,
            States          => This.Configs.Available_State_Entity_Ids,
            Planning_States => Get_PlanningStates_Ids (Request))
        and then
            Check_For_Required_Operating_Region_And_Keepin_Keepout_Zones
           (Operating_Region  => Get_OperatingRegion_From_OriginalRequest (Request),
            Operating_Regions => This.Configs.Available_Operating_Regions,
            KeepIn_Zones_Ids  => This.Configs.Available_KeepIn_Zones_Ids,
            KeepOut_Zones_Ids => This.Configs.Available_KeepOut_Zones_Ids)));

      -- check for required tasks and task requirements
      declare
         TaskIds : constant Int64_Vect := Get_TaskList_From_OriginalRequest (Request);
      begin
         for I in First_Index (TaskIds) .. Last_Index (TaskIds) loop
            pragma Loop_Invariant
              (IsReady =
                 (IsReady'Loop_Entry and then
                 (for all K in First_Index (TaskIds) .. I - 1 =>
                      Int64_CMASI_Task_Maps.Contains
                         (This.Configs.Available_Tasks, Element (TaskIds, K))
                       and then Check_For_Specific_Task_Requirements
                         (Available_Area_of_Interest_Ids  => This.Configs.Available_Area_of_Interest_Ids,
                          Available_Line_of_Interest_Ids  => This.Configs.Available_Line_of_Interest_Ids,
                          Available_Point_of_Interest_Ids => This.Configs.Available_Point_of_Interest_Ids,
                          ItTask                          => Int64_CMASI_Task_Maps.Element
                                 (This.Configs.Available_Tasks, Element (TaskIds, K))))));
            declare
               use Int64_CMASI_Task_Maps;
               TaskId : constant Int64 := Element (TaskIds, I);
               Pos    : constant Cursor := Find (This.Configs.Available_Tasks, TaskId);
               IsReadyPrev : constant Boolean := IsReady with Ghost;
            begin
               if Pos /= No_Element then
                  declare
                     ItTask : constant Task_Kind_And_Id :=
                       Element (This.Configs.Available_Tasks, Pos);
                     use Int64_Sets;
                  begin
                     -- check for specific task requirements
                     if ItTask.Kind = AngledAreaSearchTask then
                        if ItTask.SearchAreaID /= 0 then
                           if not Contains (This.Configs.Available_Area_of_Interest_Ids,
                                            ItTask.SearchAreaID)
                           then
                              Append (To   => ReasonForFailure,
                                      Tail => "- AreaOfInterest Id["
                                      & Int64'Image (ItTask.SearchAreaID)
                                      & "] not available.");
                              IsReady := false;
                           end if;
                        end if;
                     elsif ItTask.Kind = ImpactLineSearchTask then
                        if ItTask.LineID /= 0 then
                           if not Contains (This.Configs.Available_Line_of_Interest_Ids,
                                            ItTask.LineID)
                           then
                              Append (To   => ReasonForFailure,
                                      Tail => "- LineOfInterest Id["
                                      & Int64'Image (ItTask.LineID)
                                      & "] not available.");
                              IsReady := False;
                           end if;
                        end if;
                     elsif ItTask.Kind = ImpactPointSearchTask then
                        if ItTask.SearchLocationID /= 0 then
                           if not Contains (This.Configs.Available_Point_of_Interest_Ids,
                                            ItTask.SearchLocationID)
                           then
                              Append (To   => ReasonForFailure,
                                      --  Point of interest ??
                                      Tail => "- LineOfInterest Id["
                                      & Int64'Image (ItTask.SearchLocationID)
                                      & "] not available.");
                              IsReady := False;
                           end if;
                        end if;
                     end if;
                     pragma Assert
                       (IsReady = (IsReadyPrev and then
                        Check_For_Specific_Task_Requirements
                         (Available_Area_of_Interest_Ids  => This.Configs.Available_Area_of_Interest_Ids,
                          Available_Line_of_Interest_Ids  => This.Configs.Available_Line_of_Interest_Ids,
                          Available_Point_of_Interest_Ids => This.Configs.Available_Point_of_Interest_Ids,
                          ItTask                          => ItTask)));
                  end;
               else
                  pragma Assert (not Int64_CMASI_Task_Maps.Contains
                                 (This.Configs.Available_Tasks, TaskId));
                  Append (To   => ReasonForFailure,
                          Tail => "- Task with the Id[" & Int64'Image (TaskId)
                          & "] is unknown. Ensure task description preceeds automation request.");
                  IsReady := False;
               end if;
               pragma Assert
                 (IsReady = (IsReadyPrev and then
                  Int64_CMASI_Task_Maps.Contains
                    (This.Configs.Available_Tasks, Element (TaskIds, I))
                  and then Check_For_Specific_Task_Requirements
                    (Available_Area_of_Interest_Ids  => This.Configs.Available_Area_of_Interest_Ids,
                     Available_Line_of_Interest_Ids  => This.Configs.Available_Line_of_Interest_Ids,
                     Available_Point_of_Interest_Ids => This.Configs.Available_Point_of_Interest_Ids,
                     ItTask                          => Int64_CMASI_Task_Maps.Element
                            (This.Configs.Available_Tasks, Element (TaskIds, I)))));
            end;
         end loop;
      end;
      pragma Assert (IsReady = Valid_Automation_Request (This.Configs, Request));

      if not IsReady then
         declare
            ErrResponseID : Int64;
            Old_Confs : constant Configuration_Data := This.Configs with Ghost;
            Old_Pending_Request : constant UniqueAutomationRequest_Lists.Formal_Model.M.Sequence :=
              UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests) with Ghost;
            Old_Waiting_Request : constant UniqueAutomationRequest_Lists.Formal_Model.M.Sequence :=
              UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks) with Ghost;
         begin
            Send_Error_Response (This, Request, ReasonForFailure, ErrResponseID);
            Prove_Validity_Preserved (Old_Confs, This.Configs, Request);
            Prove_Validity_Preserved (Old_Confs, Old_Pending_Request, UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests));
            Prove_Validity_Preserved (Old_Confs, Old_Waiting_Request, UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks));
            Prove_Validity_Preserved (Old_Confs, This.Configs, UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests));
            Prove_Validity_Preserved (Old_Confs, This.Configs, UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks));

            Int64_Request_Details_Maps.Delete (This.Sandbox, ErrResponseID);
         end;
      end if;
   end Check_Automation_Request_Requirements;

end UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation.SPARK;




















































with UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation; use UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation;
with afrl.impact.AngledAreaSearchTask;
with afrl.impact.ImpactLineSearchTask;
with afrl.impact.ImpactPointSearchTask;
with afrl.cmasi.lmcpTask.SPARK_Boundary; use afrl.cmasi.lmcpTask.SPARK_Boundary;
with afrl.impact.ImpactAutomationRequest; use afrl.impact.ImpactAutomationRequest;
with afrl.impact.ImpactAutomationRequest.SPARK_Boundary; use afrl.impact.ImpactAutomationRequest.SPARK_Boundary;
with uxas.messages.lmcptask.TaskAutomationRequest; use uxas.messages.lmcptask.TaskAutomationRequest;
with uxas.messages.lmcptask.TaskAutomationRequest.SPARK_Boundary; use uxas.messages.lmcptask.TaskAutomationRequest.SPARK_Boundary;
with afrl.cmasi.AutomationRequest; use afrl.cmasi.AutomationRequest;
with afrl.cmasi.AutomationRequest.SPARK_Boundary; use afrl.cmasi.AutomationRequest.SPARK_Boundary;
with avtas.lmcp.object.SPARK_Boundary; use avtas.lmcp.object.SPARK_Boundary;
with Ada.Containers; use Ada.Containers;

private
package UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation.SPARK with SPARK_Mode is
   use all type Int64_Vect;
   use all type Int64_Set;
   use all type CMASI_Task_Map;
   use all type Operating_Region_Maps;
   use all type UniqueAutomationRequest_Ref_Deque;

   --------------------------------------
   -- Functions for annotation purpose --
   --------------------------------------

   function All_Elements_In (V : Int64_Vect; S : Int64_Set) return Boolean is
     (for all J in Int64_Vects.First_Index (V) .. Int64_Vects.Last_Index (V)
      => Int64_Sets.Contains (S, Int64_Vects.Element (V, J)))
   with Ghost;

   function Check_For_Required_Entity_Configurations
     (Entity_Ids      : Int64_Vect;
      Configurations  : Int64_Set;
      States          : Int64_Set;
      Planning_States : Int64_Vect) return Boolean
   is

      --  Check that we have a configuration and a state for each required
      --  entity.

     (All_Elements_In (Entity_Ids, Configurations)
       and then

      --  States should be either in in the states registered in the service,
      --  or in the planning states of the request.

        (for all J in Int64_Vects.First_Index (Entity_Ids) ..
             Int64_Vects.Last_Index (Entity_Ids)
         =>
             (Int64_Sets.Contains
              (States, Int64_Vects.Element (Entity_Ids, J))
              or else

              --  [Claire]: to be checked that this is the expected semantics,
              --  the handling of Planning_States seems strange to me.

                (not Int64_Sets.Is_Empty (States)
                 and then Int64_Vects.Contains
                   (Planning_States, Int64_Vects.Element (Entity_Ids, J)))))

      --  If no entities are required, check that there is at least a
      --  configuration and a matching state.

      and then
        (if Int64_Vects.Is_Empty (Entity_Ids)
         then (for some Id of Configurations =>
                    Int64_Sets.Contains (States, Id))))
   with Ghost;

   function Check_For_Required_Operating_Region_And_Keepin_Keepout_Zones
     (Operating_Region  : Int64;
      Operating_Regions : Operating_Region_Maps;
      KeepIn_Zones_Ids  : Int64_Set;
      KeepOut_Zones_Ids : Int64_Set) return Boolean
   is
      -- check for required operating region and keepin/keepout zones
     (if Operating_Region /= 0
      then Int64_Operating_Region_Maps.Contains
        (Operating_Regions, Operating_Region)
      and then All_Elements_In
        ((Int64_Operating_Region_Maps.Element
                  (Operating_Regions, Operating_Region).KeepInAreas),
         KeepIn_Zones_Ids)
      and then All_Elements_In
        ((Int64_Operating_Region_Maps.Element
                  (Operating_Regions, Operating_Region).KeepOutAreas),
         KeepOut_Zones_Ids))
   with Ghost;

   function Check_For_Specific_Task_Requirements
     (Available_Area_of_Interest_Ids  : Int64_Set;
      Available_Line_of_Interest_Ids  : Int64_Set;
      Available_Point_of_Interest_Ids : Int64_Set;
      ItTask                          : Task_Kind_And_Id) return Boolean
   is
     (case ItTask.Kind is
         when AngledAreaSearchTask  =>
            ItTask.SearchAreaID = 0
      or else Int64_Sets.Contains (Available_Area_of_Interest_Ids, ItTask.SearchAreaID),
         when ImpactLineSearchTask  =>
            ItTask.LineID = 0
      or else Int64_Sets.Contains (Available_Line_of_Interest_Ids, ItTask.LineID),
         when ImpactPointSearchTask =>
            itTask.SearchLocationID = 0
      or else Int64_Sets.Contains (Available_Point_of_Interest_Ids, itTask.SearchLocationID),
         when Other_Task            => True)
   with Ghost,
     Global => null;

   function Check_For_Required_Tasks_And_Task_Requirements
     (Available_Tasks                 : CMASI_Task_Map;
      Available_Area_of_Interest_Ids  : Int64_Set;
      Available_Line_of_Interest_Ids  : Int64_Set;
      Available_Point_of_Interest_Ids : Int64_Set;
      TaskIds                         : Int64_Vect) return Boolean
   is
     (for all K in Int64_Vects.First_Index (TaskIds) ..
          Int64_Vects.Last_Index (TaskIds)
      =>
         Int64_CMASI_Task_Maps.Contains
        (Available_Tasks, Int64_Vects.Element (TaskIds, K))
      and then Check_For_Specific_Task_Requirements
        (Available_Area_of_Interest_Ids,
         Available_Line_of_Interest_Ids,
         Available_Point_of_Interest_Ids,
         Int64_CMASI_Task_Maps.Element
                (Available_Tasks, Int64_Vects.Element (TaskIds, K))))
   with Ghost,
     Global => null;
   pragma Annotate (GNATprove, Inline_For_Proof, Check_For_Required_Tasks_And_Task_Requirements);

   function Valid_Automation_Request
     (This    : Configuration_Data;
      Request : My_UniqueAutomationRequest) return Boolean
   is
     (Check_For_Required_Entity_Configurations
       (Entity_Ids      => Get_EntityList_From_OriginalRequest (Request),
        Configurations  => This.Available_Configuration_Entity_Ids,
        States          => This.Available_State_Entity_Ids,
        Planning_States => Get_PlanningStates_Ids (Request))

       and then Check_For_Required_Operating_Region_And_Keepin_Keepout_Zones
         (Operating_Region  => Get_OperatingRegion_From_OriginalRequest (Request),
          Operating_Regions => This.Available_Operating_Regions,
          KeepIn_Zones_Ids  => This.Available_KeepIn_Zones_Ids,
          KeepOut_Zones_Ids => This.Available_KeepOut_Zones_Ids)

      and then Check_For_Required_Tasks_And_Task_Requirements
        (Available_Tasks                 => This.Available_Tasks,
         Available_Area_of_Interest_Ids  => This.Available_Area_of_Interest_Ids,
         Available_Line_of_Interest_Ids  => This.Available_Line_of_Interest_Ids,
         Available_Point_of_Interest_Ids => This.Available_Point_of_Interest_Ids,
         TaskIds                         => Get_TaskList_From_OriginalRequest (Request)))
   with Ghost,
     Global => null;
   pragma Annotate (GNATprove, Inline_For_Proof, Valid_Automation_Request);

   function Get_EntityList_From_Request
     (Request : Object'Class) return Int64_Vect
   is (if Request in ImpactAutomationRequest
       then Get_EntityList_From_TrialRequest (ImpactAutomationRequest (Request))
       elsif Request in TaskAutomationRequest
       then Get_EntityList_From_OriginalRequest (TaskAutomationRequest (Request))
       else Get_EntityList (AutomationRequest (Request)))
   with Ghost,
     Pre => Request in
       AutomationRequest | ImpactAutomationRequest | TaskAutomationRequest;

   function Empty_Vector return Int64_Vect with Ghost,
     Post => Int64_Vects.Is_Empty (Empty_Vector'Result);

   function Get_OperatingRegion_From_Request
     (Request : Object'Class) return Int64
   is (if Request in ImpactAutomationRequest
       then Get_OperatingRegion_From_TrialRequest (ImpactAutomationRequest (Request))
       elsif Request in TaskAutomationRequest
       then Get_OperatingRegion_From_OriginalRequest (TaskAutomationRequest (Request))
       else Get_OperatingRegion (AutomationRequest (Request)))
   with Ghost,
     Pre => Request in
       AutomationRequest | ImpactAutomationRequest | TaskAutomationRequest;

   function Get_TaskList_From_Request
     (Request : Object'Class) return Int64_Vect
   is (if Request in ImpactAutomationRequest
       then Get_TaskList_From_TrialRequest (ImpactAutomationRequest (Request))
       elsif Request in TaskAutomationRequest
       then Get_TaskList_From_OriginalRequest (TaskAutomationRequest (Request))
       else Get_TaskList (AutomationRequest (Request)))
   with Ghost,
     Pre => Request in
       AutomationRequest | ImpactAutomationRequest | TaskAutomationRequest;

   function Get_PlanningStates_Ids_From_Request
     (Request : Object'Class) return Int64_Vect
   is (if Request in ImpactAutomationRequest
       then Empty_Vector
       elsif Request in TaskAutomationRequest
       then Get_PlanningStates_Ids (TaskAutomationRequest (Request))
       else Empty_Vector)
   with Ghost,
     Pre => Request in
       AutomationRequest | ImpactAutomationRequest | TaskAutomationRequest;

   function Is_Corresponding_UniqueRequest
     (UniqueRequest : My_UniqueAutomationRequest;
      Request       : Object'Class) return Boolean
   is
     (Get_PlanningStates_Ids (UniqueRequest) =
          Get_PlanningStates_Ids_From_Request (Request)
      and then Get_EntityList_From_OriginalRequest (UniqueRequest) =
          Get_EntityList_From_Request (Request)
      and then Get_OperatingRegion_From_OriginalRequest (UniqueRequest) =
          Get_OperatingRegion_From_Request (Request)
      and then Get_TaskList_From_OriginalRequest (UniqueRequest) =
          Get_TaskList_From_Request (Request))
   with Ghost,
     Pre => Request in
       AutomationRequest | ImpactAutomationRequest | TaskAutomationRequest;

   function Valid_Request
     (This    : Configuration_Data;
      Request : Object'Class) return Boolean
   is
     (Check_For_Required_Entity_Configurations
       (Entity_Ids      => Get_EntityList_From_Request (Request),
        Configurations  => This.Available_Configuration_Entity_Ids,
        States          => This.Available_State_Entity_Ids,
        Planning_States => Get_PlanningStates_Ids_From_Request (Request))

       and then Check_For_Required_Operating_Region_And_Keepin_Keepout_Zones
         (Operating_Region  => Get_OperatingRegion_From_Request (Request),
          Operating_Regions => This.Available_Operating_Regions,
          KeepIn_Zones_Ids  => This.Available_KeepIn_Zones_Ids,
          KeepOut_Zones_Ids => This.Available_KeepOut_Zones_Ids)

       and then Check_For_Required_Tasks_And_Task_Requirements
        (Available_Tasks                 => This.Available_Tasks,
         Available_Area_of_Interest_Ids  => This.Available_Area_of_Interest_Ids,
         Available_Line_of_Interest_Ids  => This.Available_Line_of_Interest_Ids,
         Available_Point_of_Interest_Ids => This.Available_Point_of_Interest_Ids,
         TaskIds                         => Get_TaskList_From_Request (Request)))
   with Ghost,
     Pre => Request in
       AutomationRequest | ImpactAutomationRequest | TaskAutomationRequest;

   function All_Requests_Valid
     (This : Automation_Request_Validator_Service) return Boolean
   is ((for all R of This.Pending_Requests =>
          Valid_Automation_Request (This.Configs, R.Content))
       and then (for all R of This.Requests_Waiting_For_Tasks =>
          Valid_Automation_Request (This.Configs, R.Content)))
   with Ghost;

   function Same_Requests (K, L : UniqueAutomationRequest_Lists.Formal_Model.M.Sequence) return Boolean
   is
     (UniqueAutomationRequest_Lists.Formal_Model.M.Length (K) = UniqueAutomationRequest_Lists.Formal_Model.M.Length (L)
      and then
        (for all I in 1 .. UniqueAutomationRequest_Lists.Formal_Model.M.Length (K) =>
              UxAS.Messages.LmcpTask.UniqueAutomationRequest.SPARK_Boundary.Same_Requests
                (UniqueAutomationRequest_Lists.Formal_Model.Element (K, I).Content,
                 UniqueAutomationRequest_Lists.Formal_Model.Element (L, I).Content)))
     with Ghost;

   -------------------------------------
   -- Regular Service Functionalities --
   -------------------------------------

   procedure Check_Tasks_Initialized
     (This : in out Automation_Request_Validator_Service)
   with Post =>
       (if All_Requests_Valid (This)'Old then All_Requests_Valid (This));
   --  Everything is preserved but Request queues. We did not express this in
   --  the contract yet.

   procedure Check_Automation_Request_Requirements
     (This    : in out Automation_Request_Validator_Service;
      Request : My_UniqueAutomationRequest;
      IsReady : out Boolean)
   --  Turned into a procedure as it has side effects on This
   with Post =>

     --  Meaning of IsReady

       IsReady = Valid_Automation_Request (This.Configs, Request)

     --  Preservation of components of This. Everything is preserved but
     --  This.sandbox. For now, I only added information
     --  necessary to prove that validity of requests is preserved.

     --  Preservation of the request queues: we do not use equality as it is
     --  not known by SPARK.

     and Same_Requests
       (UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks),
        UniqueAutomationRequest_Lists.Formal_Model.Model (This.Requests_Waiting_For_Tasks)'Old)
     and Same_Requests
       (UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests),
        UniqueAutomationRequest_Lists.Formal_Model.Model (This.Pending_Requests)'Old)
     and (if All_Requests_Valid (This)'Old then All_Requests_Valid (This))

     and This.Configs'Old = This.Configs;

   procedure Handle_Automation_Request
     (This         : in out Automation_Request_Validator_Service;
      Auto_Request : My_Object_Any)
   with Pre => Deref (Auto_Request) in
     AutomationRequest | ImpactAutomationRequest | TaskAutomationRequest,
       Post =>
         (if All_Requests_Valid (This)'Old then All_Requests_Valid (This));

end UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation.SPARK;

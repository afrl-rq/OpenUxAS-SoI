with Common_Formal_Containers; use Common_Formal_Containers;
with afrl.cmasi.AutomationRequest.SPARK_Boundary; use afrl.cmasi.AutomationRequest.SPARK_Boundary;
with afrl.impact.ImpactAutomationRequest; use afrl.impact.ImpactAutomationRequest;
with afrl.impact.ImpactAutomationRequest.SPARK_Boundary; use afrl.impact.ImpactAutomationRequest.SPARK_Boundary;
with avtas.lmcp.object.SPARK_Boundary; use avtas.lmcp.object.SPARK_Boundary;
with uxas.messages.lmcptask.TaskAutomationRequest; use uxas.messages.lmcptask.TaskAutomationRequest;
with uxas.messages.lmcptask.TaskAutomationRequest.SPARK_Boundary; use uxas.messages.lmcptask.TaskAutomationRequest.SPARK_Boundary;

package UxAS.Messages.LmcpTask.UniqueAutomationRequest.SPARK_Boundary with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   --  This package introduces a wrapper around UniqueAutomationRequest.
   --  UniqueAutomationRequest is a private type, so it can be used in SPARK.
   --  This wrapper is only used to introduce contracts on the type and
   --  its accessors.

   use all type Int64_Vect;

   type My_UniqueAutomationRequest is private with
     Default_Initial_Condition =>
       Int64_Vects.Is_Empty (Get_PlanningStates_Ids (My_UniqueAutomationRequest));

   function Get_EntityList_From_OriginalRequest
     (Request : My_UniqueAutomationRequest) return Int64_Vect
     with Global => null;

   function Get_OperatingRegion_From_OriginalRequest
     (Request : My_UniqueAutomationRequest) return Int64
     with Global => null;

   function Get_PlanningStates_Ids
     (Request : My_UniqueAutomationRequest) return Int64_Vect
     with Global => null;

   function getRequestID
     (this : My_UniqueAutomationRequest) return Int64
     with Global => null;

   function Get_TaskList_From_OriginalRequest
     (Request : My_UniqueAutomationRequest) return Int64_Vect
     with Global => null;

   function Same_Requests (X, Y : My_UniqueAutomationRequest) return Boolean is
     (Get_PlanningStates_Ids (X) = Get_PlanningStates_Ids (Y)
      and Get_EntityList_From_OriginalRequest (X) =
          Get_EntityList_From_OriginalRequest (Y)
      and Get_OperatingRegion_From_OriginalRequest (X) =
          Get_OperatingRegion_From_OriginalRequest (Y)
      and Get_TaskList_From_OriginalRequest (X) =
          Get_TaskList_From_OriginalRequest (Y));
   pragma Annotate (GNATprove, Inline_For_Proof, Same_Requests);

   overriding function "=" (X, Y : My_UniqueAutomationRequest) return Boolean with
     Global => null,
     Post => (if "="'Result then Same_Requests (X, Y));

   procedure Copy_PlanningState_From_TaskAutomationRequest
     (Target : in out My_UniqueAutomationRequest;
      Source : uxas.messages.lmcptask.TaskAutomationRequest.TaskAutomationRequest)
     with Global => null,
     Post => Get_PlanningStates_Ids (Target) =
     Get_PlanningStates_Ids (Source)
     and Get_EntityList_From_OriginalRequest (Target) =
     Get_EntityList_From_OriginalRequest (Target)'Old
     and Get_OperatingRegion_From_OriginalRequest (Target) =
     Get_OperatingRegion_From_OriginalRequest (Target)'Old
     and Get_TaskList_From_OriginalRequest (Target) =
     Get_TaskList_From_OriginalRequest (Target)'Old;

   procedure Copy_OriginalRequest_From_ImpactAutomationRequest
     (Target : in out My_UniqueAutomationRequest;
      Source : ImpactAutomationRequest)
     with Global => null,
     Post => Get_EntityList_From_OriginalRequest (Target) =
     Get_EntityList_From_TrialRequest (Source)
     and Get_OperatingRegion_From_OriginalRequest (Target) =
     Get_OperatingRegion_From_TrialRequest (Source)
     and Get_TaskList_From_OriginalRequest (Target) =
     Get_TaskList_From_TrialRequest (Source)
     and Get_PlanningStates_Ids (Target) =
     Get_PlanningStates_Ids (Target)'Old;

   procedure Copy_OriginalRequest_From_AutomationRequest
     (Target : in out My_UniqueAutomationRequest;
      Source : My_Object_Any)
   with Global => null,
     Pre => Deref (Source) in AutomationRequest,
     Post => Get_EntityList_From_OriginalRequest (Target) =
     Get_EntityList (AutomationRequest (Deref (Source)))
     and Get_OperatingRegion_From_OriginalRequest (Target) =
     Get_OperatingRegion (AutomationRequest (Deref (Source)))
     and Get_TaskList_From_OriginalRequest (Target) =
     Get_TaskList (AutomationRequest (Deref (Source)))
     and Get_PlanningStates_Ids (Target) =
     Get_PlanningStates_Ids (Target)'Old;

   procedure Copy_OriginalRequest_From_TaskAutomationRequest
     (Target : in out My_UniqueAutomationRequest;
      Source : uxas.messages.lmcptask.TaskAutomationRequest.TaskAutomationRequest)
     with Global => null,
     Post => Get_EntityList_From_OriginalRequest (Target) =
     Get_EntityList_From_OriginalRequest (Source)
     and Get_OperatingRegion_From_OriginalRequest (Target) =
     Get_OperatingRegion_From_OriginalRequest (Source)
     and Get_TaskList_From_OriginalRequest (Target) =
     Get_TaskList_From_OriginalRequest (Source)
     and Get_PlanningStates_Ids (Target) =
     Get_PlanningStates_Ids (Target)'Old;

   procedure setRequestID
     (this : in out My_UniqueAutomationRequest; RequestID : in Int64)
     with Global => null,
     Post => getRequestID (This) = RequestID
     and Get_EntityList_From_OriginalRequest (This) =
     Get_EntityList_From_OriginalRequest (This)'Old
     and Get_PlanningStates_Ids (This) =
     Get_PlanningStates_Ids (This)'Old
     and Get_OperatingRegion_From_OriginalRequest (This) =
     Get_OperatingRegion_From_OriginalRequest (This)'Old
     and Get_TaskList_From_OriginalRequest (This) =
     Get_TaskList_From_OriginalRequest (This)'Old;

   procedure setSandBoxRequest
     (this           : in out My_UniqueAutomationRequest;
      SandBoxRequest : Boolean)
     with Global => null,
     Post => Get_EntityList_From_OriginalRequest (This) =
     Get_EntityList_From_OriginalRequest (This)'Old
     and Get_PlanningStates_Ids (This) =
     Get_PlanningStates_Ids (This)'Old
     and Get_OperatingRegion_From_OriginalRequest (This) =
     Get_OperatingRegion_From_OriginalRequest (This)'Old
     and Get_TaskList_From_OriginalRequest (This) =
     Get_TaskList_From_OriginalRequest (This)'Old;
   --  Simple renaming to add a contract

   function Unwrap (this : My_UniqueAutomationRequest) return UniqueAutomationRequest;

   function Wrap (this : UniqueAutomationRequest) return My_UniqueAutomationRequest;
private
   pragma SPARK_Mode (Off);
   type My_UniqueAutomationRequest is record
      Content : UniqueAutomationRequest;
   end record;

   overriding function "=" (X, Y : My_UniqueAutomationRequest) return Boolean is
     (X.Content = Y.Content);

   function getRequestID (this : My_UniqueAutomationRequest) return Int64 is
     (this.Content.getRequestID);

   function Unwrap (this : My_UniqueAutomationRequest) return UniqueAutomationRequest is
     (this.Content);

   function Wrap (this : UniqueAutomationRequest) return My_UniqueAutomationRequest is
     (Content => this);
end UxAS.Messages.LmcpTask.UniqueAutomationRequest.SPARK_Boundary;

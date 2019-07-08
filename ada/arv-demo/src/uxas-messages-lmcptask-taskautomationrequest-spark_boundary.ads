with Common_Formal_Containers; use Common_Formal_Containers;
package uxas.messages.Lmcptask.TaskAutomationRequest.SPARK_Boundary with SPARK_Mode is

   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   function Get_EntityList_From_OriginalRequest
     (Request : TaskAutomationRequest) return Int64_Vect
     with Global => null;

   function Get_OperatingRegion_From_OriginalRequest
     (Request : TaskAutomationRequest) return Int64
     with Global => null;

   function Get_PlanningStates_Ids
     (Request : TaskAutomationRequest) return Int64_Vect
     with Global => null;

   function Get_TaskList_From_OriginalRequest
     (Request : TaskAutomationRequest) return Int64_Vect
     with Global => null;
end uxas.messages.Lmcptask.TaskAutomationRequest.SPARK_Boundary;

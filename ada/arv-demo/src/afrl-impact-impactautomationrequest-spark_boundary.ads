with Common_Formal_Containers; use Common_Formal_Containers;
package afrl.impact.ImpactAutomationRequest.SPARK_Boundary with SPARK_Mode is

   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   function Get_EntityList_From_TrialRequest
     (Request : ImpactAutomationRequest) return Int64_Vect
     with Global => null;

   function Get_OperatingRegion_From_TrialRequest
     (Request : ImpactAutomationRequest) return Int64
     with Global => null;

   function Get_TaskList_From_TrialRequest
     (Request : ImpactAutomationRequest) return Int64_Vect
     with Global => null;
end afrl.impact.ImpactAutomationRequest.SPARK_Boundary;

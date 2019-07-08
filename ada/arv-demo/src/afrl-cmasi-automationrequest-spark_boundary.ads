with Common_Formal_Containers; use Common_Formal_Containers;
package afrl.cmasi.AutomationRequest.SPARK_Boundary with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   function Get_EntityList
     (Request : AutomationRequest) return Int64_Vect
     with Global => null;

   function Get_OperatingRegion
     (Request : AutomationRequest) return Int64
     with Global => null;

   function Get_TaskList
     (Request : AutomationRequest) return Int64_Vect
     with Global => null;
end afrl.cmasi.AutomationRequest.SPARK_Boundary;

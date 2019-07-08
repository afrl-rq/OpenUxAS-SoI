package body afrl.impact.ImpactAutomationRequest.SPARK_Boundary with SPARK_Mode => Off is

   --------------------------------------
   -- Get_EntityList_From_TrialRequest --
   --------------------------------------

   function Get_EntityList_From_TrialRequest
     (Request : ImpactAutomationRequest) return Int64_Vect
   is
      L : constant Vect_Int64_Acc := Request.getTrialRequest.getEntityList;
   begin
      return R : Int64_Vect do
         for E of L.all loop
            Int64_Vects.Append (R, E);
         end loop;
      end return;
   end Get_EntityList_From_TrialRequest;

   ----------------------------------------------
   -- Get_OperatingRegion_From_TrialRequest --
   ----------------------------------------------

   function Get_OperatingRegion_From_TrialRequest
     (Request : ImpactAutomationRequest) return Int64
   is (Request.getTrialRequest.getOperatingRegion);

   ------------------------------------
   -- Get_TaskList_From_TrialRequest --
   ------------------------------------

   function Get_TaskList_From_TrialRequest
     (Request : ImpactAutomationRequest) return Int64_Vect
   is
      L : constant Vect_Int64_Acc := Request.getTrialRequest.getTaskList;
   begin
      return R : Int64_Vect do
         for E of L.all loop
            Int64_Vects.Append (R, E);
         end loop;
      end return;
   end Get_TaskList_From_TrialRequest;
end afrl.impact.ImpactAutomationRequest.SPARK_Boundary;

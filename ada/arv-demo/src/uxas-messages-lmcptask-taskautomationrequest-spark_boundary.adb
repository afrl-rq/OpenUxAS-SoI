package body uxas.messages.Lmcptask.TaskAutomationRequest.SPARK_Boundary with SPARK_Mode => Off is

   -----------------------------------------
   -- Get_EntityList_From_OriginalRequest --
   -----------------------------------------

   function Get_EntityList_From_OriginalRequest
     (Request : TaskAutomationRequest) return Int64_Vect
   is
      L : constant Vect_Int64_Acc := Request.getOriginalRequest.getEntityList;
   begin
      return R : Int64_Vect do
         for E of L.all loop
            Int64_Vects.Append (R, E);
         end loop;
      end return;
   end Get_EntityList_From_OriginalRequest;

   ----------------------------------------------
   -- Get_OperatingRegion_From_OriginalRequest --
   ----------------------------------------------

   function Get_OperatingRegion_From_OriginalRequest
     (Request : TaskAutomationRequest) return Int64
   is (Request.getOriginalRequest.getOperatingRegion);

   ----------------------------
   -- Get_PlanningStates_Ids --
   ----------------------------

   function Get_PlanningStates_Ids
     (Request : TaskAutomationRequest) return Int64_Vect
   is
      L : constant Vect_PlanningState_Acc_Acc :=
        Request.getPlanningStates;
   begin
      return R : Int64_Vect do
         for E of L.all loop
            Int64_Vects.Append (R, E.getEntityID);
         end loop;
      end return;
   end Get_PlanningStates_Ids;

   ---------------------------------------
   -- Get_TaskList_From_OriginalRequest --
   ---------------------------------------

   function Get_TaskList_From_OriginalRequest
     (Request : TaskAutomationRequest) return Int64_Vect
   is
      L : constant Vect_Int64_Acc := Request.getOriginalRequest.getTaskList;
   begin
      return R : Int64_Vect do
         for E of L.all loop
            Int64_Vects.Append (R, E);
         end loop;
      end return;
   end Get_TaskList_From_OriginalRequest;

end uxas.messages.Lmcptask.TaskAutomationRequest.SPARK_Boundary;

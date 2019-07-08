package body UxAS.Messages.LmcpTask.UniqueAutomationRequest.SPARK_Boundary with SPARK_Mode => Off is

   ---------------------------------------------------
   -- Copy_PlanningState_From_TaskAutomationRequest --
   ---------------------------------------------------

   procedure Copy_PlanningState_From_TaskAutomationRequest
     (Target : in out My_UniqueAutomationRequest;
      Source : uxas.messages.lmcptask.TaskAutomationRequest.TaskAutomationRequest)
   is
   begin
      for planningState of Source.getPlanningStates.all loop
         uxas.messages.lmcptask.UniqueAutomationRequest.Vect_PlanningState_Acc.Append (Target.Content.getPlanningStates.all, planningState); --  we need to do a clone here
      end loop;
   end Copy_PlanningState_From_TaskAutomationRequest;

   -------------------------------------------
   -- Copy_OriginalRequest_From_AutomationRequest --
   -------------------------------------------

   procedure Copy_OriginalRequest_From_AutomationRequest
     (Target : in out My_UniqueAutomationRequest;
      Source : My_Object_Any)
   is
   begin
      Target.Content.setOriginalRequest (AutomationRequest_Acc (Unwrap (Source)));
   end Copy_OriginalRequest_From_AutomationRequest;

   -------------------------------------------------------
   -- Copy_OriginalRequest_From_ImpactAutomationRequest --
   -------------------------------------------------------

   procedure Copy_OriginalRequest_From_ImpactAutomationRequest
     (Target : in out My_UniqueAutomationRequest;
      Source : ImpactAutomationRequest)
   is
   begin
      Target.Content.setOriginalRequest (Source.getTrialRequest); --  we need to do a clone here
   end Copy_OriginalRequest_From_ImpactAutomationRequest;

   -----------------------------------------------------
   -- Copy_OriginalRequest_From_TaskAutomationRequest --
   -----------------------------------------------------

   procedure Copy_OriginalRequest_From_TaskAutomationRequest
     (Target : in out My_UniqueAutomationRequest;
      Source : uxas.messages.lmcptask.TaskAutomationRequest.TaskAutomationRequest)
   is
   begin
      Target.Content.setOriginalRequest (Source.getOriginalRequest); --  we need to do a clone here
   end Copy_OriginalRequest_From_TaskAutomationRequest;

   -----------------------------------------
   -- Get_EntityList_From_OriginalRequest --
   -----------------------------------------

   function Get_EntityList_From_OriginalRequest
     (Request : My_UniqueAutomationRequest) return Int64_Vect
   is
      L : constant Vect_Int64_Acc := Request.Content.getOriginalRequest.getEntityList;
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
     (Request : My_UniqueAutomationRequest) return Int64
   is (Request.Content.getOriginalRequest.getOperatingRegion);

   ----------------------------
   -- Get_PlanningStates_Ids --
   ----------------------------

   function Get_PlanningStates_Ids
     (Request : My_UniqueAutomationRequest) return Int64_Vect
   is
      L : constant uxas.messages.Lmcptask.UniqueAutomationRequest.Vect_PlanningState_Acc_Acc :=
        Request.Content.getPlanningStates;
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
     (Request : My_UniqueAutomationRequest) return Int64_Vect
   is
      L : constant Vect_Int64_Acc := Request.Content.getOriginalRequest.getTaskList;
   begin
      return R : Int64_Vect do
         for E of L.all loop
            Int64_Vects.Append (R, E);
         end loop;
      end return;
   end Get_TaskList_From_OriginalRequest;

   ------------------
   -- setRequestID --
   ------------------

   procedure setRequestID
     (this      : in out My_UniqueAutomationRequest;
      RequestID : Int64)
   is
   begin
      this.Content.setRequestID (RequestID);
   end setRequestID;

   -----------------------
   -- setSandBoxRequest --
   -----------------------

   procedure setSandBoxRequest
     (this           : in out My_UniqueAutomationRequest;
      SandBoxRequest : Boolean)
   is
   begin
      this.Content.setSandBoxRequest (SandBoxRequest);
   end setSandBoxRequest;

end UxAS.Messages.LmcpTask.UniqueAutomationRequest.SPARK_Boundary;

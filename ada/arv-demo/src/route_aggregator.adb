package body Route_Aggregator with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   pragma Assertion_Policy (Ignore);

   --  Lemmas used to factor out reasonning about the redefined model of
   --  Int64_Formal_Set_Maps

   -------------------
   -- Model_Include --
   -------------------

   procedure Model_Include
     (M1, M2 : Int64_Formal_Set_Maps.Formal_Model.M.Map;
      N1, N2 : Int_Set_Maps_M.Map)
   --  Lemma: Inclusion of old models implies inclusion of redefined models

   with Ghost,
     Global => null,
     Pre  => Same_Mappings (M1, N1) and Same_Mappings (M2, N2) and M1 <= M2,
     Post => N1 <= N2
   is
   begin
      null;
   end Model_Include;

   -----------------------------
   -- Lift_From_Keys_To_Model --
   -----------------------------

   procedure Lift_From_Keys_To_Model (PendingRoute : Int64_Formal_Set_Map)
   --  Lemma: Lift quantification done on Keys of the pending route map to its
   --  model.

   with Ghost,
     Global => null,
     Post =>
       (for all Key of Model (pendingRoute) =>
          (Find (Keys (pendingRoute), Key) > 0
           and then Int_Set_Maps_K.Get (Keys (pendingRoute), Find (Keys (pendingRoute), Key)) =
             Key))
   is
   begin
      null;
   end Lift_From_Keys_To_Model;

   --  Subprograms wraping insertion and deletion in m_pendingRoute. They
   --  restate part of the postcondition of the callee, but also reestablish
   --  the predicate of Route_Aggregator_State and compute the effect of the
   --  modification on planToRoute.

   -------------------------
   -- Insert_PendingRoute --
   -------------------------

   procedure Insert_PendingRoute
     (m_pendingRoute   : in out Int64_Formal_Set_Map;
      m_routeRequestId : Int64;
      RequestID        : int64;
      PlanRequests     : Int64_Formal_Set)
   with Pre => not Int_Set_Maps_M.Has_Key (Model (m_pendingRoute), RequestID)
       and Length (m_pendingRoute) < m_pendingRoute.Capacity
       and
         All_Pending_Routes_Seen (Model (m_pendingRoute), m_routeRequestId)
       and
         No_Overlaps (Model (m_pendingRoute))
       and
         (for all Id of PlanRequests => Id <= m_routeRequestId)
       and
       (for all R_Id of Model (m_pendingRoute) =>
          (for all E of Int_Set_Maps_M.Get (Model (m_pendingRoute), R_Id) => not Contains (PlanRequests, E))),
     Post =>

     --  Predicate of State

       All_Pending_Routes_Seen (Model (m_pendingRoute), m_routeRequestId)
     and No_Overlaps (Model (m_pendingRoute))

     --  Part of the postcondition copied from Int64_Formal_Set_Maps.Insert

     and Model (m_pendingRoute)'Old <= Model (m_pendingRoute)
     and Contains (Model (m_pendingRoute), RequestID)
     and (for all E of Int_Set_Maps_M.Get (Model (m_pendingRoute), RequestID) =>
            Contains (PlanRequests, E))
     and (for all E of PlanRequests => Contains (Int_Set_Maps_M.Get (Model (m_pendingRoute), RequestID), E))
     and (for all K of Model (m_pendingRoute) =>
              Int_Set_Maps_M.Has_Key (Model (m_pendingRoute)'Old, K)
          or K = RequestID)

     --  Effect on planToRoute

     and planToRoute (m_pendingRoute)'Old <= planToRoute (m_pendingRoute)
     and (for all I of PlanRequests =>
            Has_Key (planToRoute (m_pendingRoute), I)
          and then Get (planToRoute (m_pendingRoute), I) = RequestID)
     and (for all I of planToRoute (m_pendingRoute) =>
              Contains (PlanRequests, I) or Has_Key (planToRoute (m_pendingRoute)'Old, I))
   is
      Old_pendingRoute   : constant Int_Set_Maps_M.Map := Model (m_pendingRoute) with Ghost;
      Old_pendingRoute_M : constant Int64_Formal_Set_Maps.Formal_Model.M.Map :=
        Int64_Formal_Set_Maps.Formal_Model.Model (m_pendingRoute) with Ghost;
   begin
      Insert (m_pendingRoute, RequestID, PlanRequests);

      --  Establish the effect on the redefined Model of maps of formal sets

      Model_Include
        (Old_pendingRoute_M, Int64_Formal_Set_Maps.Formal_Model.Model (m_pendingRoute),
         Old_pendingRoute, Model (m_pendingRoute));
      pragma Assert (for all K of Model (m_pendingRoute) =>
                       Int_Set_Maps_M.Has_Key (Old_pendingRoute, K)
                     or K = RequestID);
      pragma Assert (No_Overlaps (Model (m_pendingRoute)));
   end Insert_PendingRoute;

   -------------------------
   -- Delete_PendingRoute --
   -------------------------

   procedure Delete_PendingRoute
     (m_pendingRoute   : in out Int64_Formal_Set_Map;
      m_routeRequestId : Int64;
      Position         : in out Int64_Formal_Set_Maps.Cursor)
     with Pre => Has_Element (m_pendingRoute, Position)
     and All_Pending_Routes_Seen (Model (m_pendingRoute), m_routeRequestId)
     and No_Overlaps (Model (m_pendingRoute)),

       Post =>

     --  Predicate of State

        All_Pending_Routes_Seen (Model (m_pendingRoute), m_routeRequestId)
     and No_Overlaps (Model (m_pendingRoute))

     --  Postcondition copied from Int64_Formal_Set_Maps.Delete

     and Length (m_pendingRoute) = Length (m_pendingRoute)'Old - 1
     and not Int_Set_Maps_M.Has_Key (Model (m_pendingRoute), Key (m_pendingRoute, Position)'Old)
     and not Int_Set_Maps_P.Has_Key (Positions (m_pendingRoute), Position'Old)
     and Model (m_pendingRoute) <= Model (m_pendingRoute)'Old
     and Int_Set_Maps_M.Keys_Included_Except
       (Model (m_pendingRoute)'Old,
        Model (m_pendingRoute),
        Key (m_pendingRoute, Position)'Old)
     and Int_Set_Maps_K.Range_Equal
       (Left  => Keys (m_pendingRoute)'Old,
        Right => Keys (m_pendingRoute),
        Fst   => 1,
        Lst   => Int_Set_Maps_P.Get (Positions (m_pendingRoute)'Old, Position'Old) - 1)
     and Int_Set_Maps_K.Range_Shifted
       (Left   => Keys (m_pendingRoute),
        Right  => Keys (m_pendingRoute)'Old,
        Fst    => Int_Set_Maps_P.Get (Positions (m_pendingRoute)'Old, Position'Old),
        Lst    => Length (m_pendingRoute),
        Offset => 1)
     and P_Positions_Shifted
       (Positions (m_pendingRoute),
        Positions (m_pendingRoute)'Old,
        Cut   => Int_Set_Maps_P.Get (Positions (m_pendingRoute)'Old, Position'Old))

     --  Effect on planToRoute

     and planToRoute (m_pendingRoute) <= planToRoute (m_pendingRoute)'Old
     and (for all I of planToRoute (m_pendingRoute)'Old =>
              Has_Key (planToRoute (m_pendingRoute), I)
          or else Get (planToRoute (m_pendingRoute)'Old, I) = Key (m_pendingRoute, Position)'Old)
   is
      Old_pendingRoute_M : constant Int64_Formal_Set_Maps.Formal_Model.M.Map :=
        Int64_Formal_Set_Maps.Formal_Model.Model (m_pendingRoute) with Ghost;
      Old_pendingRoute   : constant Int_Set_Maps_M.Map := Model (m_pendingRoute) with Ghost;
   begin
      Delete (m_pendingRoute, Position);

      --  Establish the effect on the redefined Model of maps of formal sets

      Model_Include
        (Int64_Formal_Set_Maps.Formal_Model.Model (m_pendingRoute), Old_pendingRoute_M,
         Model (m_pendingRoute), Old_pendingRoute);
   end Delete_PendingRoute;

   --  Model functions used in contracts

   -----------
   -- Model --
   -----------

   function Model (M : Int64_Formal_Set_Map) return Int_Set_Maps_M.Map is
      function Model (S : Int64_Formal_Set) return Int64_Set with
        Post =>
          (for all E of Model'Result => Contains (S, E))
          and
            (for all E of S => Contains (Model'Result, E))
      is
         Res : Int64_Set;
      begin
         for C in S loop
            pragma Loop_Variant (Increases => Int_Set_P.Get (Positions (S), C));
            pragma Loop_Invariant (Length (Res) = Int_Set_P.Get (Positions (S), C) - 1);
            pragma Loop_Invariant (for all E of Res => Contains (S, E));
            pragma Loop_Invariant
              (for all K in 1 .. Int_Set_P.Get (Positions (S), C) - 1 =>
                 Contains (Res, Int_Set_E.Get (Elements (S), K)));
            pragma Loop_Invariant
              (for all K in Int_Set_P.Get (Positions (S), C) .. Length (S) =>
                    not Contains (Res, Int_Set_E.Get (Elements (S), K)));
            Res := Add (Res, Element (S, C));
         end loop;
         return Res;
      end Model;

      Res : Int_Set_Maps_M.Map;
   begin
      for C in M loop
         pragma Loop_Variant (Increases => Int_Set_Maps_P.Get (Positions (M), C));
         pragma Loop_Invariant (Int_Set_Maps_M.Length (Res) = Int_Set_Maps_P.Get (Positions (M), C) - 1);
         pragma Loop_Invariant (for all I of Res => Contains (M, I));
         pragma Loop_Invariant
           (for all I of Res =>
              (for all E of Int_Set_Maps_M.Get (Res, I) =>
                   Contains (Element (M, I), E)));
         pragma Loop_Invariant
           (for all I of Res =>
              (for all E of Element (M, I) =>
                   Contains (Int_Set_Maps_M.Get (Res, I), E)));
         pragma Loop_Invariant
           (for all K in 1 .. Int_Set_Maps_P.Get (Positions (M), C) - 1 =>
                 Int_Set_Maps_M.Has_Key (Res, Int_Set_Maps_K.Get (Keys (M), K)));
         pragma Loop_Invariant
           (for all K in Int_Set_Maps_P.Get (Positions (M), C) .. Length (M) =>
                 not Int_Set_Maps_M.Has_Key (Res, Int_Set_Maps_K.Get (Keys (M), K)));
         Res := Int_Set_Maps_M.Add (Res, Key (M, C), Model (Element (M, C)));
      end loop;
      return Res;
   end Model;

   -----------------
   -- planToRoute --
   -----------------

   function PlanToRoute (PendingRoute : Int64_Formal_Set_Map) return Int64_Map is
      Res : Int64_Map;
   begin
      for C in pendingRoute loop
         pragma Loop_Variant (Increases => Int_Set_Maps_P.Get (Positions (pendingRoute), C));
         pragma Loop_Invariant
           (for all I of Res =>
              Int_Set_Maps_M.Has_Key (Model (pendingRoute), Get (Res, I))
            and then Contains (Int_Set_Maps_M.Get (Model (pendingRoute), Get (Res, I)), I));
         pragma Loop_Invariant
           (for all J in 1 .. Int_Set_Maps_P.Get (Positions (pendingRoute), C) - 1 =>
              (for all K of Int_Set_Maps_M.Get (Model (pendingRoute), Int_Set_Maps_K.Get (Keys (pendingRoute), J)) =>
                   Has_Key (Res, K)
               and then Get (Res, K) = Int_Set_Maps_K.Get (Keys (pendingRoute), J)));
         pragma Loop_Invariant
           (for all J in Int_Set_Maps_P.Get (Positions (pendingRoute), C) .. Length (pendingRoute) =>
              (for all K of Int_Set_Maps_M.Get (Model (pendingRoute), Int_Set_Maps_K.Get (Keys (pendingRoute), J)) =>
                   not Has_Key (Res, K)));

         declare
            routePlans : Int64_Formal_Set renames Element (pendingRoute, C);
         begin
            for C2 in routePlans loop
               pragma Loop_Variant (Increases => Int_Set_P.Get (Positions (routePlans), C2));
               pragma Loop_Invariant
                 (for all I of Res =>
                    Int_Set_Maps_M.Has_Key (Model (pendingRoute), Get (Res, I))
                  and then Contains (Int_Set_Maps_M.Get (Model (pendingRoute), Get (Res, I)), I));
               pragma Loop_Invariant
                 (for all J in 1 .. Int_Set_Maps_P.Get (Positions (pendingRoute), C) - 1 =>
                    (for all K of Int_Set_Maps_M.Get (Model (pendingRoute), Int_Set_Maps_K.Get (Keys (pendingRoute), J)) =>
                         Has_Key (Res, K)
                     and then Get (Res, K) = Int_Set_Maps_K.Get (Keys (pendingRoute), J)));
               pragma Loop_Invariant
                 (for all J in Int_Set_Maps_P.Get (Positions (pendingRoute), C) + 1 .. Length (pendingRoute) =>
                      (for all K of Int_Set_Maps_M.Get (Model (pendingRoute), Int_Set_Maps_K.Get (Keys (pendingRoute), J)) =>
                            not Has_Key (Res, K)));
               pragma Loop_Invariant
                 (for all J in 1 .. Int_Set_P.Get (Positions (routePlans), C2) - 1 =>
                         Has_Key (Res, Int_Set_E.Get (Elements (routePlans), J))
                     and then Get (Res, Int_Set_E.Get (Elements (routePlans), J)) = Key (pendingRoute, C));
               pragma Loop_Invariant
                 (for all J in Int_Set_P.Get (Positions (routePlans), C2) .. Length (routePlans) =>
                         not Has_Key (Res, Int_Set_E.Get (Elements (routePlans), J)));

               pragma Assume (Length (Res) < Count_Type'Last, "We have less than Count_Type'Last pending plan requests in total");
               Res := Add (Res, Element (routePlans, C2), Key (pendingRoute, C));
            end loop;
         end;
      end loop;
      return Res;
   end planToRoute;

   --------------------------------
   -- Handle_Route_Plan_Response --
   --------------------------------

   --  Actual implementation of the service

   procedure Handle_Route_Plan_Response
     (Mailbox  : in out Route_Aggregator_Mailbox;
      State    : in out Route_Aggregator_State;
      Response : RoutePlanResponse)
   is
      OldHistory : constant History_Type := History with Ghost;
   begin
      pragma Assume (Length (History) < Count_Type'Last, "We still have room for a new event in History");
      History := Add (History, (Kind => Receive_PlanResponse, Id => Response.ResponseID));

      pragma Assume (Length (State.m_routePlanResponses) < State.m_routePlanResponses.Capacity, "We have some room for a new plan response");
      Insert (State.m_routePlanResponses, Response.ResponseID, Response);
      pragma Assert (Valid_Plan_Responses (State.m_pendingRoute, State.m_routePlanResponses));
      pragma Assert
        (Only_Pending_Plans (State.m_routePlanResponses, State.m_routePlans));

      for p in 1 .. Last (Response.RouteResponses) loop

         --  All plans are registered up to p

         pragma Loop_Invariant
           (for all RP of Model (State.m_routePlanResponses) =>
              (if RP /= Response.ResponseID then
                   (for all Pl of Element (State.m_routePlanResponses, RP).RouteResponses =>
                          Contains (State.m_routePlans, Pl.RouteID)
                    and then Element (State.m_routePlans, Pl.RouteID).Id = RP)));
         pragma Loop_Invariant
           (for all K in 1 .. p - 1 =>
              Contains (State.m_routePlans, Get (Response.RouteResponses, K).RouteID)
            and then Element (State.m_routePlans, Get (Response.RouteResponses, K).RouteID).Id = Response.ResponseID);
         pragma Loop_Invariant
           (for all K in p .. Last (Response.RouteResponses) =>
              not Contains (State.m_routePlans, Get (Response.RouteResponses, K).RouteID));

         --  Invariants

         pragma Loop_Invariant
           (Only_Pending_Plans (State.m_routePlanResponses, State.m_routePlans));

         pragma Assume (Length (State.m_routePlans) < State.m_routePlans.Capacity, "We have enough room for all route plans");
         Insert (State.m_routePlans, Get (Response.RouteResponses, p).RouteID,
                 IdPlanPair'(Id   => Response.ResponseID,
                             Plan => Get (Response.RouteResponses, p)));
         pragma Assert (Contains (Element (State.m_routePlanResponses, Response.ResponseID).RouteResponses, Get (Response.RouteResponses, p).RouteID));
      end loop;

      pragma Assert (No_RouteRequest_Lost (State.m_pendingRoute));
      pragma Assert (for all Pl of Element (State.m_routePlanResponses, Response.ResponseID).RouteResponses =>
                       Contains (State.m_routePlans, Pl.RouteID)
                     and then Element (State.m_routePlans, Pl.RouteID).Id = Response.ResponseID);
      pragma Assert (for all RP of Model (State.m_routePlanResponses) =>
                       (for all Pl of Element (State.m_routePlanResponses, RP).RouteResponses =>
                            Contains (State.m_routePlans, Pl.RouteID)
                        and then Element (State.m_routePlans, Pl.RouteID).Id = RP));
      Check_All_Route_Plans (Mailbox, State);
   end Handle_Route_Plan_Response;

   --------------------------
   -- Handle_Route_Request --
   --------------------------

   procedure Handle_Route_Request
     (Data    : Route_Aggregator_Configuration_Data;
      Mailbox : in out Route_Aggregator_Mailbox;
      State   : in out Route_Aggregator_State;
      Request : RouteRequest)
   is
      use Int64_Sequences;
      Vehicle_Ids  : Int64_Seq := Request.VehicleID;
      PlanRequests : Int64_Formal_Set;
      Old_routeRequestId : constant Int64 := State.m_routeRequestId with Ghost;
   begin
      pragma Assume (Length (History) < Count_Type'Last, "We still have room for a new event in History");
      History := Add (History, (Kind => Receive_RouteRequest, Id => Request.RequestID));

      if Length (Vehicle_Ids) = 0 then
         Vehicle_Ids := Data.m_entityStates;
      end if;

      --  We only have route plan responses with Ids smaller than State.m_routeRequestId

      pragma Assert
        (for all K of Model (State.m_routePlanResponses) =>
                Contains (Int_Set_Maps_M.Get (Model (State.m_pendingRoute), Get (planToRoute (State.m_pendingRoute), K)), K));
      pragma Assert
        (for all K of Model (State.m_routePlanResponses) =>
             K <= State.m_routeRequestId);
      pragma Assert
        (for all E of History =>
           (if E.Kind = Receive_PlanResponse then
                 E.Id <= State.m_routeRequestId));

      for K in 1 .. Last (Vehicle_Ids) loop

         --  We are only adding to planrequests new request ids

         pragma Loop_Invariant
           (State.m_routeRequestId'Loop_Entry <= State.m_routeRequestId);
         pragma Loop_Invariant
           (for all Id of Model (PlanRequests) => Id > State.m_routeRequestId'Loop_Entry
            and Id <= State.m_routeRequestId);
         pragma Loop_Invariant
           (for all Id of Model (State.m_pendingRoute) =>
              (for all K of Int_Set_Maps_M.Get (Model (State.m_pendingRoute), Id) =>
                   K <= State.m_routeRequestId'Loop_Entry));
         pragma Loop_Invariant (Length (PlanRequests) <= Count_Type (K - 1));

         --  If fast planning is used, we may already have some responses for the
         --  new plan requests.

         pragma Loop_Invariant
           (for all K of Model (State.m_routePlanResponses) =>
                Contains (Model (State.m_routePlanResponses)'Loop_Entry, K)
            or else (Data.m_fastPlan and then Contains (PlanRequests, K)));

         --  General Invariants

         pragma Loop_Invariant
           (All_Plans_Registered (State.m_routePlanResponses, State.m_routePlans));
         pragma Loop_Invariant
           (Only_Pending_Plans (State.m_routePlanResponses, State.m_routePlans));
         pragma Loop_Invariant
           (No_Finished_Route_Request (State.m_pendingRoute, State.m_routePlanResponses));

         --  Update of the history, it may contain new plan requests

         pragma Loop_Invariant (History'Loop_Entry <= History);
         pragma Loop_Invariant
           (for all I in 1 .. Last (History) =>
                (if I >  Last (History)'Loop_Entry then
                        Get (History, I).Kind = Send_PlanRequest));

         --  History Invariants

         pragma Loop_Invariant (Valid_Events (State.m_routeRequestId));
         pragma Loop_Invariant
           (No_PlanResponse_Lost (State.m_pendingRoute, State.m_routePlanResponses));
         pragma Loop_Invariant
           (All_Pending_Plans_Sent (State.m_pendingRoute, State.m_routePlanResponses));
         pragma Loop_Invariant
           (for all Id of Model (PlanRequests) =>
              PlanRequest_Processed (State.m_routePlanResponses, Id));

         declare
            Vehicle_Id  : Int64 renames Get (Vehicle_Ids, K);

            -- create a new route plan request

            pragma Assume (State.m_routeRequestId < int64'Last, "The request ID does not overflow");
            planRequest : constant RoutePlanRequest :=
              (AssociatedTaskID  => Request.AssociatedTaskID,
               IsCostOnlyRequest => Request.IsCostOnlyRequest,
               OperatingRegion   => Request.OperatingRegion,
               VehicleID         => Vehicle_Id,
               RequestID         => State.m_routeRequestId + 1,
               RouteRequests     => Request.RouteRequests);
         begin

            State.m_routeRequestId := State.m_routeRequestId + 1;

            pragma Assume (Length (PlanRequests) < PlanRequests.Capacity, "We have enough room for all vehicles in planRequests");
            Insert (PlanRequests, planRequest.RequestID);

            if Contains (Data.m_groundVehicles, vehicle_Id) then
               if Data.m_fastPlan then
                  -- short-circuit and just plan with straight line planner

                  Euclidean_Plan (Data,
                                  State.m_routePlanResponses,
                                  State.m_routePlans,
                                  planRequest);
               else

                  -- send externally

                  sendLimitedCastMessage
                    (Mailbox, GroundPathPlanner, planRequest);
                  pragma Assume (Length (History) < Count_Type'Last, "We still have room for a new event in History");
                  History := Add (History, (Kind => Send_PlanRequest, Id => planRequest.RequestID));
                  pragma Assert (PlanRequest_Sent (planRequest.RequestID));
               end if;
            else
               pragma Assert
                 (Contains (Data.m_airVehicles, Vehicle_Id)
                  or else Contains (Data.m_surfaceVehicles, Vehicle_Id));

               -- send to aircraft planner

               sendLimitedCastMessage
                 (Mailbox, AircraftPathPlanner, planRequest);
               pragma Assume (Length (History) < Count_Type'Last, "We still have room for a new event in History");
               History := Add (History, (Kind => Send_PlanRequest, Id => planRequest.RequestID));
               pragma Assert (PlanRequest_Sent (planRequest.RequestID));
            end if;
         end;
         pragma Assert
           (for all Id of Model (PlanRequests) =>
              PlanRequest_Processed (State.m_routePlanResponses, Id));
      end loop;

      --  Restate part of the loop invariants after the loop

      pragma Assert
        (No_Finished_Route_Request (State.m_pendingRoute, State.m_routePlanResponses));
      pragma Assert (All_Pending_Plans_Sent (State.m_pendingRoute, State.m_routePlanResponses));
      pragma Assert
        (for all E of History =>
           (if E.Kind = Receive_PlanResponse then not Contains (PlanRequests, E.Id)));
      pragma Assert
        (for all R_Id of Model (State.m_pendingRoute) =>
             (for all E of Int_Set_Maps_M.Get (Model (State.m_pendingRoute), R_Id) =>
                   not Contains (PlanRequests, E)));

      pragma Assume (Length (State.m_pendingRoute) < State.m_pendingRoute.Capacity, "We have enough room for a new pending route request");
      Insert_PendingRoute
        (State.m_pendingRoute, State.m_routeRequestId, Request.RequestID, PlanRequests);

      --  System invariants have been reestablished

      pragma Assert (All_Pending_Plans_Sent (State.m_pendingRoute, State.m_routePlanResponses));
      pragma Assert (Valid_Plan_Responses (State.m_pendingRoute, State.m_routePlanResponses));
      pragma Assert
        (No_PlanResponse_Lost (State.m_pendingRoute, State.m_routePlanResponses));

      -- if fast planning, then all routes should be complete; kick off response

      if Data.m_fastPlan then
         Check_All_Route_Plans (Mailbox, State);
      else
         pragma Assert (Is_Pending (Model (State.m_pendingRoute), Model (State.m_routePlanResponses), Request.RequestID));
         pragma Assert (No_Finished_Route_Request (State.m_pendingRoute, State.m_routePlanResponses));
      end if;
   end Handle_Route_Request;

   ---------------------------
   -- Check_All_Route_Plans --
   ---------------------------

   procedure Check_All_Route_Plans
     (Mailbox : in out Route_Aggregator_Mailbox;
      State   : in out Route_Aggregator_State)
   is
      i : Int64_Formal_Set_Maps.Cursor := First (State.m_pendingRoute);
      Old_routePlanResponses : RR_Maps_M.Map := Model (State.m_routePlanResponses) with Ghost;
      D : Count_Type := 0 with Ghost;
      --  Number of removed elements
   begin
      -- check pending route requests
      while Has_Element (State.m_pendingRoute, i) loop
         pragma Loop_Invariant (Has_Element (State.m_pendingRoute, i));

         pragma Loop_Invariant
           (D = Length (State.m_pendingRoute)'Loop_Entry - Length (State.m_pendingRoute));
         pragma Loop_Invariant
           (Model (State.m_pendingRoute) <= Int_Set_Maps_M.Map'(Model (State.m_pendingRoute))'Loop_Entry);
         pragma Loop_Invariant
           (for all K in 1 .. Int_Set_Maps_P.Get (Positions (State.m_pendingRoute), I) - 1 =>
              (for some L in 1 .. Int_Set_Maps_P.Get (Positions (State.m_pendingRoute), I) - 1 + D =>
                    Int_Set_Maps_K.Get (Keys (State.m_pendingRoute), K) = Int_Set_Maps_K.Get (Keys (State.m_pendingRoute)'Loop_Entry, L)));
         pragma Loop_Invariant
           (for all K in 1 .. Int_Set_Maps_P.Get (Positions (State.m_pendingRoute), I) - 1 =>
              Is_Pending (Model (State.m_pendingRoute), Model (State.m_routePlanResponses), Int_Set_Maps_K.Get (Keys (State.m_pendingRoute), K)));
         pragma Loop_Invariant
           (for all K in Int_Set_Maps_P.Get (Positions (State.m_pendingRoute), I) .. Length (State.m_pendingRoute) =>
              Int_Set_Maps_K.Get (Keys (State.m_pendingRoute), K) = Int_Set_Maps_K.Get (Keys (State.m_pendingRoute)'Loop_Entry, K + D));

         --  General invariants

         pragma Loop_Invariant
           (All_Plans_Registered (State.m_routePlanResponses, State.m_routePlans));
         pragma Loop_Invariant
           (Only_Pending_Plans (State.m_routePlanResponses, State.m_routePlans));
         pragma Loop_Invariant
           (Valid_Plan_Responses (State.m_pendingRoute, State.m_routePlanResponses));

         --  History invariants

         pragma Loop_Invariant (History'Loop_Entry <= History);
         pragma Loop_Invariant (Valid_Events (State.m_routeRequestId));
         pragma Loop_Invariant (No_RouteRequest_Lost (State.m_pendingRoute));
         pragma Loop_Invariant (No_PlanResponse_Lost (State.m_pendingRoute, State.m_routePlanResponses));
         pragma Loop_Invariant (All_Pending_Plans_Sent (State.m_pendingRoute, State.m_routePlanResponses));

         declare
            isFulfilled : constant Boolean :=
              (for all J of Element (State.m_pendingRoute, i) =>
                   Contains (State.m_routePlanResponses, j));
         begin
            if isFulfilled then
               SendRouteResponse (Mailbox, State.m_pendingRoute, State.m_routePlanResponses, State.m_routePlans, Key (State.m_pendingRoute, i));

               declare
                  Dummy    : Int64_Formal_Set_Maps.Cursor := i;
                  Pos      : constant Count_Type := Int_Set_Maps_P.Get (Positions (State.m_pendingRoute), I) with Ghost;
               begin
                  Next (State.m_pendingRoute, i);
                  Delete_PendingRoute (State.m_pendingRoute, State.m_routeRequestId, Dummy);
                  D := D + 1;
                  pragma Assert
                    (for all K in 1 .. Pos - 1 =>
                       Is_Pending (Model (State.m_pendingRoute), Model (State.m_routePlanResponses), Int_Set_Maps_K.Get (Keys (State.m_pendingRoute), K)));
               end;
               pragma Assert (All_Pending_Plans_Sent (State.m_pendingRoute, State.m_routePlanResponses));

            else
               Next (State.m_pendingRoute, i);
            end if;
         end;
      end loop;

      --  Restablish No_Finished_Route_Request

      pragma Assert
        (for all K in 1 .. Length (State.m_pendingRoute) =>
             Is_Pending (Model (State.m_pendingRoute), Model (State.m_routePlanResponses), Int_Set_Maps_K.Get (Keys (State.m_pendingRoute), K)));
      Lift_From_Keys_To_Model (State.m_pendingRoute);


      --  Remove for now, we only care about RouteRequest
      --
      -- check pending automation requests
      --      auto k = m_pendingAutoReq.begin();
      --      while (k != m_pendingAutoReq.end())
      --      {
      --          bool isFulfilled = true;
      --          for (const int64_t& j : k->second)
      --          {
      --              if (m_routePlans.find(j) == m_routePlans.end())
      --              {
      --                  isFulfilled = false;
      --                  break;
      --              }
      --          }
      --
      --          if (isFulfilled)
      --          {
      --              SendMatrix(k->first);
      --              // finished with this automation request, discard
      --              m_uniqueAutomationRequests.erase(k->first);
      --              k = m_pendingAutoReq.erase(k);
      --          }
      --          else
      --          {
      --              k++;
      --          }
      --      }
   end Check_All_Route_Plans;

   -----------------------
   -- SendRouteResponse --
   -----------------------

   procedure SendRouteResponse
     (Mailbox            : in out Route_Aggregator_Mailbox;
      pendingRoute       : Int64_Formal_Set_Map;
      routePlanResponses : in out Int64_RouteResponse_Map;
      routePlans         : in out Int64_IdPlanPair_Map;
      routeKey           : Int64)
   is
      Response  : RouteResponse;
      PlanResponses : Int64_Formal_Set renames Element (pendingRoute, routeKey);
      Old_routePlanResponses : constant RR_Maps_M.Map := Model (routePlanResponses) with Ghost;
   begin
      response.ResponseID := routeKey;
      for Cu in PlanResponses loop

         --  Number of elements added to response.Routes

         pragma Loop_Invariant (Length (response.Routes) < Int_Set_P.Get (Positions (PlanResponses), Cu));

         --  We have removed all elements of PlanResponses from routePlanResponses
         --  up to Cu.

         pragma Loop_Invariant
           (for all I in 1 .. Int_Set_P.Get (Positions (PlanResponses), Cu) - 1 =>
              not Contains (routePlanResponses, Int_Set_E.Get (Elements (PlanResponses), I)));
         pragma Loop_Invariant
           (for all I in Int_Set_P.Get (Positions (PlanResponses), Cu) .. Length (PlanResponses) =>
              Contains (routePlanResponses, Int_Set_E.Get (Elements (PlanResponses), I)));
         pragma Loop_Invariant
           (for all Id of Old_routePlanResponses =>
              (if not Contains (PlanResponses, Id) then
                    Contains (routePlanResponses, Id)));
         pragma Loop_Invariant
           (for all Id of Model (routePlanResponses) =>
                Contains (Old_routePlanResponses, Id));

         --  Invariants

         pragma Loop_Invariant
           (Valid_Plan_Responses (pendingRoute, routePlanResponses));
         pragma Loop_Invariant
           (All_Plans_Registered (routePlanResponses, routePlans));
         pragma Loop_Invariant
           (Only_Pending_Plans (routePlanResponses, routePlans));

         --  History invariants:
         --  We have only removed responses associated to routeKey

         pragma Loop_Invariant
           (for all Id of planToRoute (pendingRoute) =>
                (if Get (planToRoute (pendingRoute), Id) /= routeKey then
                      Contains (routePlanResponses, Id)
                 or else PlanRequest_Sent (Id)));
         pragma Loop_Invariant
           (for all E of History =>
              (if E.Kind = Receive_PlanResponse
               and then Has_Key (planToRoute (pendingRoute), E.Id)
               and then Get (planToRoute (pendingRoute), E.Id) /= routeKey
               then Contains (routePlanResponses, E.Id)));

         declare
            rId : Int64 renames Element (PlanResponses, Cu);
         begin

            declare
               plan : Int64_RouteResponse_Maps.Cursor := Find (routePlanResponses, rId);

               --  NB. The if statement checking whether rId is in
               --  routePlanResponses was removed as SendRouteResponse is only
               --  called when all plan responses have been received.
               pragma Assert (Has_Element (routePlanResponses, plan));

               resps : RP_Seq renames Element (routePlanResponses, plan).RouteResponses;
            begin
               response.Routes := Add (response.Routes, Element (routePlanResponses, plan));

               -- delete all individual routes from storage

               for i in 1 .. Last (resps) loop

                  --  We have removed all elements of resps from routePlans
                  --  up to i.

                  pragma Loop_Invariant
                    (for all RP of Model (routePlanResponses) =>
                       (if RP /= rId then
                            (for all Pl of Element (routePlanResponses, RP).RouteResponses =>
                                   Contains (routePlans, Pl.RouteID)
                             and then Element (routePlans, Pl.RouteID).Id = RP)));
                  pragma Loop_Invariant
                    (Only_Pending_Plans (routePlanResponses, routePlans));
                  pragma Loop_Invariant
                    (for all Pl of Model (routePlans) =>
                       (if Element (routePlans, Pl).Id = rId then
                            (for some K in i .. Last (resps) =>
                                   Get (resps, K).RouteID = Pl)));
                  pragma Loop_Invariant
                    (for all K in i .. Last (resps) =>
                       Contains (routePlans, Get (resps, K).RouteID)
                     and then Element (routePlans, Get (resps, K).RouteID).Id = rId);

                  --  We only delete plans associated to rId
                  pragma Assert (Element (routePlans, Get (resps, i).RouteID).Id = rId);
                  Delete (routePlans, Get (resps, i).RouteID);
               end loop;

               pragma Assert
                 (for all Pl of Model (routePlans) =>  Element (routePlans, Pl).Id /= rId);
               Delete (routePlanResponses, plan);
               pragma Assert
                 (Only_Pending_Plans (routePlanResponses, routePlans));
            end;
         end;
      end loop;
      pragma Assert (All_Plans_Registered (routePlanResponses, routePlans));
      pragma Assert
        (for all Id of planToRoute (pendingRoute) =>
             (if Get (planToRoute (pendingRoute), Id) /= routeKey then
                   Contains (routePlanResponses, Id)
              or else PlanRequest_Sent (Id)));

      -- send the results of the query
      sendBroadcastMessage(Mailbox, Response);
      pragma Assume (Length (History) < Count_Type'Last, "We still have room for a new event in History");
      History := Add (History, (Kind => Send_RouteResponse, Id => Response.ResponseID));
   end SendRouteResponse;

   --------------------
   -- Euclidean_Plan --
   --------------------

   procedure Euclidean_Plan
     (Data               : Route_Aggregator_Configuration_Data;
      routePlanResponses : in out Int64_RouteResponse_Map;
      routePlans         : in out Int64_IdPlanPair_Map;
      Request            : RoutePlanRequest)
   is
   begin
      pragma Compile_Time_Warning (Standard.True, "Euclidean_Plan is unimplemented");
      raise Program_Error with "Euclidean_Plan is unimplemented";
   end Euclidean_Plan;

end Route_Aggregator;

with Route_Aggregator_Common;
with AFRL.CMASI.Enumerations;
with AVTAS.LMCP.Types;
with UxAS.Messages.Route.RouteResponse;  use UxAS.Messages.Route.RouteResponse;

package body Route_Aggregator_Message_Conversions is

   function As_RouteConstraints_Acc (Msg : Route_Aggregator_Messages.RouteConstraints) return RouteConstraints_Acc;

   ------------------------------
   -- As_VehicleAction_Message --
   ------------------------------

   function As_VehicleAction_Message
     (Msg : not null VehicleAction_Any)
   return Route_Aggregator_Messages.VehicleAction
   is
      Result : Route_Aggregator_Messages.VehicleAction;
      use Route_Aggregator_Common;
   begin
      for VA of Msg.getAssociatedTaskList.all loop
        Result.AssociatedTaskList := Add (Result.AssociatedTaskList, Route_Aggregator_Common.Int64 (VA));
      end loop;
      return Result;
   end As_VehicleAction_Message;

   ----------------------
   -- As_VehicleAction --
   ----------------------

   function As_VehicleAction_Acc (Msg : Route_Aggregator_Messages.VehicleAction) return VehicleAction_Acc is
      Result : constant VehicleAction_Acc := new VehicleAction;
   begin
      for Id : Route_Aggregator_Common.Int64 of Msg.AssociatedTaskList loop
         Result.getAssociatedTaskList.Append (AVTAS.LMCP.Types.int64 (Id));
      end loop;
      return result;
   end As_VehicleAction_Acc;

   -----------------------------
   -- As_KeyValuePair_Message --
   -----------------------------

   function As_KeyValuePair_Message
     (Msg : not null KeyValuePair_Acc)
   return Route_Aggregator_Messages.KeyValuePair
   is
      Result : Route_Aggregator_Messages.KeyValuePair;
   begin
      Result.Key := Msg.GetKey;
      Result.Value := Msg.getValue;
      return Result;
   end As_KeyValuePair_Message;

   -------------------------
   -- As_KeyValuePair_Acc --
   -------------------------

   function As_KeyValuePair_Acc (Msg : Route_Aggregator_Messages.KeyValuePair) return KeyValuePair_Acc is
      Result : constant KeyValuePair_Acc := new KeyValuePair;
   begin
      Result.SetKey (Msg.Key);
      Result.setValue (Msg.Value);
      return Result;
   end As_KeyValuePair_Acc;

   -------------------------
   -- As_Waypoint_Message --
   -------------------------

   function As_Waypoint_Message
     (Msg : not null Waypoint_Any)
   return Route_Aggregator_Messages.Waypoint
   is
      Result : Route_Aggregator_Messages.Waypoint;
   begin
      --  the Location3D components
      Route_Aggregator_Messages.Location3D (Result) := As_Location3D_Message (Location3D_Any (Msg));

      --  the Waypoint extension components
      Result.Number := Route_Aggregator_Common.Int64 (Msg.GetNumber);
      Result.NextWaypoint := Route_Aggregator_Common.Int64 (Msg.getNextWaypoint);
      Result.Speed := Route_Aggregator_Common.Real32 (Msg.GetSpeed);

      case Msg.GetSpeedType is
         when Afrl.Cmasi.Enumerations.Airspeed    => Result.SpeedType := Route_Aggregator_Messages.Airspeed;
         when Afrl.Cmasi.Enumerations.Groundspeed => Result.SpeedType := Route_Aggregator_Messages.Groundspeed;
      end case;

      Result.ClimbRate := Route_Aggregator_Common.Real32 (Msg.GetClimbRate);

      case Msg.GetTurnType is
         when Afrl.Cmasi.Enumerations.TurnShort => Result.TurnType := Route_Aggregator_Messages.TurnShort;
         when Afrl.Cmasi.Enumerations.FlyOver   => Result.TurnType := Route_Aggregator_Messages.FlyOver;
      end case;

      for VA of Msg.getVehicleActionList.all loop
         Result.VehicleActionList := Route_Aggregator_Messages.Add (Result.VehicleActionList, As_VehicleAction_Message (VA));
      end loop;

      Result.ContingencyWaypointA := Route_Aggregator_Common.Int64 (Msg.GetContingencyWaypointA);
      Result.ContingencyWaypointB := Route_Aggregator_Common.Int64 (Msg.GetContingencyWaypointB);

      for Id of Msg.GetAssociatedTasks.all loop
        Result.AssociatedTasks := Route_Aggregator_Common.Add (Result.AssociatedTasks, Route_Aggregator_Common.Int64 (Id));
      end loop;

      return Result;
   end As_Waypoint_Message;

   ---------------------
   -- As_Waypoint_Acc --
   ---------------------

   function As_Waypoint_Acc (Msg : Route_Aggregator_Messages.Waypoint) return Waypoint_Acc is
      Result : constant WayPoint_Acc := new AFRL.CMASI.Waypoint.Waypoint;
   begin
      --  the Location3D components
      Result.SetLatitude (AVTAS.LMCP.Types.Real64 (Msg.Latitude));
      Result.SetLongitude (AVTAS.LMCP.Types.Real64 (Msg.Longitude));
      Result.SetAltitude (AVTAS.LMCP.Types.Real32 (Msg.Altitude));
      case Msg.AltitudeType is
         when Route_Aggregator_Messages.AGL => Result.setAltitudeType (AFRL.CMASI.Enumerations.AGL);
         when Route_Aggregator_Messages.MSL => Result.setAltitudeType (AFRL.CMASI.Enumerations.MSL);
      end case;

      --  the waypoint extensions

      Result.setNumber (AVTAS.LMCP.Types.Int64 (Msg.Number));
      Result.setNextWaypoint (AVTAS.LMCP.Types.Int64 (Msg.NextWaypoint));
      Result.SetSpeed (AVTAS.LMCP.Types.Real32 (Msg.Speed));

      case Msg.SpeedType is
         when Route_Aggregator_Messages.Airspeed    => Result.setSpeedType (AFRL.CMASI.Enumerations.Airspeed);
         when Route_Aggregator_Messages.Groundspeed => Result.setSpeedType (AFRL.CMASI.Enumerations.Groundspeed);
      end case;

      Result.setClimbRate (AVTAS.LMCP.Types.Real32 (Msg.ClimbRate));

      case Msg.TurnType is
         when Route_Aggregator_Messages.TurnShort => Result.setTurnType (AFRL.CMASI.Enumerations.TurnShort);
         when Route_Aggregator_Messages.FlyOver   => Result.setTurnType (AFRL.CMASI.Enumerations.FlyOver);
      end case;

      for VA of Msg.VehicleActionList loop
         Result.getVehicleActionList.Append (VehicleAction_Any (As_VehicleAction_Acc (VA)));
      end loop;

      Result.setContingencyWaypointA (AVTAS.LMCP.Types.Int64 (Msg.ContingencyWaypointA));
      Result.SetContingencyWaypointB (AVTAS.LMCP.Types.Int64 (Msg.ContingencyWaypointB));

      for Id of Msg.AssociatedTasks loop
         Result.getAssociatedTasks.Append (AVTAS.LMCP.Types.Int64 (Id));
      end loop;

      return Result;
   end As_Waypoint_Acc;

   ---------------------------
   -- As_Location3D_Message --
   ---------------------------

   function As_Location3D_Message
     (Msg : not null Location3D_Any)
   return Route_Aggregator_Messages.Location3D
   is
      Result : Route_Aggregator_Messages.Location3D;
   begin
      Result.Latitude := Route_Aggregator_Common.Real64 (Msg.GetLatitude);
      Result.Longitude := Route_Aggregator_Common.Real64 (Msg.GetLongitude);
      Result.Altitude := Route_Aggregator_Common.Real32 (Msg.GetAltitude);
      --  For this enumeration type component we could use 'Val and 'Pos to
      --  convert the values, but that would not be robust in the face of
      --  independent changes to either one of the two enumeration type
      --  decls, especially the order. Therefore we do an explicit comparison.
      case Msg.GetAltitudeType is
         when Afrl.Cmasi.Enumerations.AGL => Result.AltitudeType := Route_Aggregator_Messages.AGL;
         when Afrl.Cmasi.Enumerations.MSL => Result.AltitudeType := Route_Aggregator_Messages.MSL;
      end case;
      return Result;
   end As_Location3D_Message;

   -----------------------
   -- As_Location3D_Any --
   -----------------------

   function As_Location3D_Any (Msg : Route_Aggregator_Messages.Location3D) return Location3D_Any is
      Result : constant Location3D_Acc := new Location3D;
   begin
      Result.setLatitude (AVTAS.LMCP.Types.Real64 (Msg.Latitude));
      Result.setLongitude (AVTAS.LMCP.Types.Real64 (Msg.Longitude));
      Result.setAltitude (AVTAS.LMCP.Types.Real32 (Msg.Altitude));
      case Msg.AltitudeType is
         when Route_Aggregator_Messages.AGL => Result.SetAltitudeType (AFRL.CMASI.Enumerations.AGL);
         when Route_Aggregator_Messages.MSL => Result.SetAltitudeType (AFRL.CMASI.Enumerations.MSL);
      end case;

      return Location3D_Any (Result);
   end As_Location3D_Any;

   --------------------------
   -- As_RoutePlan_Message --
   --------------------------

   function As_RoutePlan_Message
     (Msg : not null RoutePlan_Any)
   return Route_Aggregator_Messages.RoutePlan
   is
      Result : Route_Aggregator_Messages.RoutePlan;
      use Route_Aggregator_Messages;
   begin
      Result.RouteID := Route_Aggregator_Common.Int64 (Msg.getRouteID);
      for WP of Msg.GetWaypoints.all loop
         Result.Waypoints := Add (Result.Waypoints, As_Waypoint_Message (WP));
      end loop;
      Result.RouteCost := Route_Aggregator_Common.Int64 (Msg.GetRouteCost);
      for Error of Msg.GetRouteError.all loop
         Result.RouteError := Add (Result.RouteError, As_KeyValuePair_Message (Error));
      end loop;
      return Result;
   end As_RoutePlan_Message;

   ----------------------------------
   -- As_RoutePlanResponse_Message --
   ----------------------------------

   function As_RoutePlanResponse_Message
     (Msg : not null RoutePlanResponse_Any)
   return Route_Aggregator_Messages.RoutePlanResponse
   is
      Result        : Route_Aggregator_Messages.RoutePlanResponse;
      New_RoutePlan : Route_Aggregator_Messages.RoutePlan;
      use Route_Aggregator_Messages;
   begin
      Result.ResponseID       := Route_Aggregator_Common.Int64 (Msg.GetResponseID);
      Result.AssociatedTaskID := Route_Aggregator_Common.Int64 (Msg.GetAssociatedTaskID);
      Result.VehicleID        := Route_Aggregator_Common.Int64 (Msg.GetVehicleID);
      Result.OperatingRegion  := Route_Aggregator_Common.Int64 (Msg.GetOperatingRegion);

      for Plan of Msg.getRouteResponses.all loop
         New_RoutePlan.RouteID   := Route_Aggregator_Common.Int64 (Plan.GetRouteID);
         New_RoutePlan.RouteCost := Route_Aggregator_Common.Int64 (Plan.GetRouteCost);

         for WP of Plan.GetWaypoints.all loop
            New_RoutePlan.Waypoints := Add (New_RoutePlan.Waypoints, As_Waypoint_Message (WP));
         end loop;

         for Error of Plan.GetRouteError.all loop
            New_RoutePlan.RouteError := Add (New_RoutePlan.RouteError, As_KeyValuePair_Message (Error));
         end loop;

         Result.RouteResponses := Add (Result.RouteResponses, New_RoutePlan);
      end loop;

      return Result;
   end As_RoutePlanResponse_Message;

   ------------------------------
   -- As_RoutePlanResponse_Acc --
   ------------------------------

   function As_RoutePlanResponse_Acc (Msg : Route_Aggregator_Messages.RoutePlanResponse'Class) return RoutePlanResponse_Acc is
      Result         : constant RoutePlanResponse_Acc := new RoutePlanResponse;
      New_Route_Plan : Uxas.Messages.Route.RoutePlan.RoutePlan_Acc;
   begin
      Result.SetResponseID (AVTAS.LMCP.Types.Int64 (Msg.ResponseID));
      Result.SetAssociatedTaskID (AVTAS.LMCP.Types.Int64 (Msg.AssociatedTaskID));
      Result.setVehicleID (AVTAS.LMCP.Types.Int64 (Msg.VehicleID));
      Result.SetOperatingRegion (AVTAS.LMCP.Types.Int64 (Msg.OperatingRegion));

      for Plan_Msg : Route_Aggregator_Messages.RoutePlan of Msg.RouteResponses loop
         New_Route_Plan := new Uxas.Messages.Route.RoutePlan.RoutePlan;

         New_Route_Plan.SetRouteID (AVTAS.LMCP.Types.Int64 (Plan_Msg.RouteID));
         New_Route_Plan.SetRouteCost (AVTAS.LMCP.Types.Int64 (Plan_Msg.RouteCost));

         --  waypoints...
         for WP : Route_Aggregator_Messages.Waypoint of Plan_Msg.Waypoints loop
            New_Route_Plan.GetWaypoints.Append (Waypoint_Any (As_Waypoint_Acc (WP)));
         end loop;

         --  route errors...
         for KVP : Route_Aggregator_Messages.KeyValuePair of Plan_Msg.RouteError loop
            New_Route_Plan.GetRouteError.Append (As_KeyValuePair_Acc (KVP));
         end loop;

         Result.getRouteResponses.Append (New_Route_Plan);
      end loop;

      return Result;
   end As_RoutePlanResponse_Acc;

   -----------------------------
   -- As_RouteRequest_Message --
   -----------------------------

   function As_RouteRequest_Message
     (Msg : not null RouteRequest_Any)
   return Route_Aggregator_Messages.RouteRequest
   is
      Result : Route_Aggregator_Messages.RouteRequest;
   begin
      Result.RequestID        := Route_Aggregator_Common.Int64 (Msg.GetRequestID);
      Result.AssociatedTaskID := Route_Aggregator_Common.Int64 (Msg.GetAssociatedTaskID);
      for VID of Msg.getVehicleID.all loop
        Result.VehicleID := Route_Aggregator_Common.Add (Result.VehicleID, Route_Aggregator_Common.Int64 (VID));
      end loop;
      Result.OperatingRegion   := Route_Aggregator_Common.Int64 (Msg.GetOperatingRegion);
      Result.IsCostOnlyRequest := Msg.GetIsCostOnlyRequest;
      for RC of Msg.getRouteRequests.all loop
        Result.RouteRequests := Route_Aggregator_Messages.Add (Result.RouteRequests, As_RouteConstraints_Message (RouteConstraints_Any (RC)));
      end loop;

      return Result;
   end As_RouteRequest_Message;

   -------------------------
   -- As_RouteRequest_Acc --
   -------------------------

   function As_RouteRequest_Acc (Msg : Route_Aggregator_Messages.RouteRequest'Class) return RouteRequest_Acc is
      Result : constant RouteRequest_Acc := new RouteRequest;
   begin
      Result.setRequestID (AVTAS.LMCP.Types.Int64 (Msg.RequestID));
      Result.setAssociatedTaskID (AVTAS.LMCP.Types.Int64 (Msg.AssociatedTaskID));
      for VID of Msg.VehicleID loop
         Result.getVehicleID.Append (AVTAS.LMCP.Types.Int64 (VID));
      end loop;
      Result.setOperatingRegion (AVTAS.LMCP.Types.Int64 (Msg.OperatingRegion));
      Result.SetIsCostOnlyRequest (Msg.IsCostOnlyRequest);
      for RC of Msg.RouteRequests loop
         Result.getRouteRequests.Append (As_RouteConstraints_Acc (RC));
      end loop;

      return Result;
   end As_RouteRequest_Acc;

   ---------------------------------
   -- As_RouteConstraints_Message --
   ---------------------------------

   function As_RouteConstraints_Message
     (Msg : not null RouteConstraints_Any)
   return Route_Aggregator_Messages.RouteConstraints
   is
      Result : Route_Aggregator_Messages.RouteConstraints;
   begin
      Result.RouteID         := Route_Aggregator_Common.Int64 (Msg.GetRouteID);
      Result.StartLocation   := As_Location3D_Message (Msg.GetStartLocation);
      Result.StartHeading    := Route_Aggregator_Common.Real32 (Msg.GetStartHeading);
      Result.UseStartHeading := Msg.GetUseStartHeading;
      Result.EndLocation     := As_Location3D_Message (Msg.GetEndLocation);
      Result.EndHeading      := Route_Aggregator_Common.Real32 (Msg.GetEndHeading);
      Result.UseEndHeading   := Msg.GetUseEndHeading;
      return Result;
   end As_RouteConstraints_Message;

   -----------------------------
   -- As_RouteConstraints_Acc --
   -----------------------------

   function As_RouteConstraints_Acc (Msg : Route_Aggregator_Messages.RouteConstraints) return RouteConstraints_Acc is
      Result : constant RouteConstraints_Acc := new RouteConstraints;
   begin
      Result.SetRouteID (AVTAS.LMCP.Types.Int64 (Msg.RouteID));
      Result.setStartLocation (As_Location3D_Any (Msg.StartLocation));
      Result.setStartHeading (AVTAS.LMCP.Types.Real32 (Msg.StartHeading));
      Result.setUseStartHeading (Msg.UseStartHeading);
      Result.setEndLocation (As_Location3D_Any (Msg.EndLocation));
      Result.setEndHeading (AVTAS.LMCP.Types.Real32 (Msg.EndHeading));
      Result.setUseEndHeading (Msg.UseEndHeading);
      return Result;
   end As_RouteConstraints_Acc;

   ---------------------------------
   -- As_RoutePlanRequest_Message --
   ---------------------------------

   function As_RoutePlanRequest_Message
     (Msg : not null RoutePlanRequest_Any)
   return Route_Aggregator_Messages.RoutePlanRequest
   is
      Result : Route_Aggregator_Messages.RoutePlanRequest;
   begin
      Result.RequestID         := Route_Aggregator_Common.Int64 (Msg.GetRequestID);
      Result.AssociatedTaskID  := Route_Aggregator_Common.Int64 (Msg.GetAssociatedTaskID);
      Result.VehicleID         := Route_Aggregator_Common.Int64 (Msg.GetVehicleID);
      Result.OperatingRegion   := Route_Aggregator_Common.Int64 (Msg.GetOperatingRegion);
      Result.IsCostOnlyRequest := Msg.GetIsCostOnlyRequest;
      for RC of Msg.getRouteRequests.all loop
        Result.RouteRequests := Route_Aggregator_Messages.Add (Result.RouteRequests, As_RouteConstraints_Message (RouteConstraints_Any (RC)));
      end loop;
      return Result;
   end As_RoutePlanRequest_Message;

   ------------------------------
   -- As_RoutePlanResponse_Acc --
   ------------------------------

   function As_RoutePlanRequest_Acc (Msg : Route_Aggregator_Messages.RoutePlanRequest'Class) return RoutePlanRequest_Acc is
      Result : constant RoutePlanRequest_Acc := new RoutePlanRequest;
   begin
      Result.SetRequestID (AVTAS.LMCP.Types.Int64 (Msg.RequestID));
      Result.SetAssociatedTaskID (AVTAS.LMCP.Types.Int64 (Msg.AssociatedTaskID));
      Result.SetVehicleID (AVTAS.LMCP.Types.Int64 (Msg.VehicleID));
      Result.SetOperatingRegion (AVTAS.LMCP.Types.Int64 (Msg.OperatingRegion));
      Result.setIsCostOnlyRequest (Msg.IsCostOnlyRequest);
      for RC : Route_Aggregator_Messages.RouteConstraints of Msg.RouteRequests loop
         Result.GetRouteRequests.Append (As_RouteConstraints_Acc (RC));
      end loop;
      return Result;
   end As_RoutePlanRequest_Acc;

   --------------------------
   -- As_RouteResponse_Acc --
   --------------------------

   function As_RouteResponse_Acc (Msg : Route_Aggregator_Messages.RouteResponse'Class) return RouteResponse_Acc is
      Result : constant RouteResponse_Acc := new RouteResponse;
   begin
      Result.SetResponseID (AVTAS.LMCP.Types.Int64 (Msg.ResponseID));
      for RP : Route_Aggregator_Messages.RoutePlanResponse of Msg.Routes loop
         Result.getRoutes.Append (As_RoutePlanResponse_Acc (RP));
      end loop;

      return Result;
   end As_RouteResponse_Acc;

   -------------------
   -- As_Object_Any --
   -------------------

   function As_Object_Any (Msg : Route_Aggregator_Messages.Message_Root'Class) return AVTAS.LMCP.Object.Object_Any is
      Result : AVTAS.LMCP.Object.Object_Any;
   begin
      --  TODO: Consider using the stream 'Write routines (not the 'Output
      --  versions) to write the message objects to a byte array, then use
      --  Unpack to get the LMCP pointer type from that. We'd need a function
      --  mapping Message_Root tags to the LMCP enumeration identifying message
      --  types (which handles the necessary ommision of writing the tags)

      if Msg in Route_Aggregator_Messages.RoutePlanRequest'Class then
         Result := AVTAS.LMCP.Object.Object_Any (As_RoutePlanRequest_Acc (Route_Aggregator_Messages.RoutePlanRequest'Class (Msg)));

      elsif Msg in Route_Aggregator_Messages.RoutePlanResponse'Class then
         Result := AVTAS.LMCP.Object.Object_Any (As_RoutePlanResponse_Acc (Route_Aggregator_Messages.RoutePlanResponse'Class (Msg)));

      elsif Msg in Route_Aggregator_Messages.RouteRequest'Class then
         Result := AVTAS.LMCP.Object.Object_Any (As_RouteRequest_Acc (Route_Aggregator_Messages.RouteRequest'Class (Msg)));

      elsif Msg in Route_Aggregator_Messages.RouteResponse'Class then
         Result := AVTAS.LMCP.Object.Object_Any (As_RouteResponse_Acc (Route_Aggregator_Messages.RouteResponse'Class (Msg)));

      else
         raise Program_Error with "unexpected message kind in Route_Aggregator_Message_Conversions.As_Object_Any";
         --  UniqueAutomationRequest is in the class but not sent
      end if;

      return Result;
   end As_Object_Any;

end Route_Aggregator_Message_Conversions;

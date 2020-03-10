with Route_Aggregator_Common;
with afrl.cmasi.enumerations;

package body Route_Aggregator_Message_Conversions is

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

      return result;
   end As_Waypoint_Message;

   ---------------------------
   -- As_Location3D_Message --
   ---------------------------

   function As_Location3D_Message
     (Msg : not null Location3D_Any)
   return Route_Aggregator_Messages.Location3D
   is
      Result : Route_Aggregator_Messages.Location3D;
   begin
      Result.Latitude     := Route_Aggregator_Common.Real64 (Msg.GetLatitude);
      Result.Latitude     := Route_Aggregator_Common.Real64 (Msg.GetLongitude);
      Result.Altitude     := Route_Aggregator_Common.Real32 (Msg.GetAltitude);
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

end Route_Aggregator_Message_Conversions;

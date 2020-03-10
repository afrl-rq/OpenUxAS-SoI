with Route_Aggregator_Common; use Route_Aggregator_Common;
with Ada.Containers.Functional_Vectors;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

package Route_Aggregator_Messages with SPARK_Mode is

   type Message_Root is abstract tagged null record;

   --  Messages only contain functional containers and SPARK compatible data

   type UniqueAutomationRequest is new Message_Root with record
      RequestID          : Int64;
      EntityList         : Int64_Seq;
      OperatingRegion    : Int64;
      PlanningStates_Ids : Int64_Seq;
      TaskList           : Int64_Seq;
   end record;

   type AltitudeTypeEnum is (AGL, MSL);
   type SpeedTypeEnum is (Airspeed, Groundspeed);
   type TurnTypeEnum is (TurnShort, FlyOver);

   type Location3D is tagged record
      -- Latitude
      Latitude : Real64 := 0.0;
      -- Longitude
      Longitude : Real64 := 0.0;
      -- Altitude for this waypoint
      Altitude : Real32 := 0.0;
      -- Altitude type for specified altitude
      AltitudeType : AltitudeTypeEnum := MSL;
   end record;

   type RouteConstraints is record
      -- ID denoting this set of route constraints
      RouteID : Int64 := 0;
      -- Location from which the planned route will start. A valid RouteConstraints message must define StartLocation (null not allowed).
      StartLocation : Location3D;
      -- Heading of entity at the start of the route
      StartHeading : Real32 := 0.0;
      -- If "true" the heading value in StartHeading must be used to start the route. If not, any starting heading can be used.
      UseStartHeading : Boolean := true;
      -- Location to which the planned route will end. A valid RouteConstraints message must define EndLocation (null not allowed).
      EndLocation : Location3D;
      -- Heading of entity at the end of the route
      EndHeading : Real32 := 0.0;
      -- If "true" the heading value in EndHeading must be used to end the route. If not, any ending heading can be used.
      UseEndHeading : Boolean := true;
   end record;

   package RC_Sequences is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => RouteConstraints);
   type RC_Seq is new RC_Sequences.Sequence;

   type VehicleAction is record
      -- A list of tasks that are associated with this action. A length of zero denotes no associated tasks. This field is for analysis purposes. The automation service should associate a list of tasks with each action to enable analysis of the allocation of tasks to vehicles.
      --
      AssociatedTaskList : Int64_Seq;
   end record;

   package VA_Sequences is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => VehicleAction);
   type VA_Seq is new VA_Sequences.Sequence;

   type Waypoint is new Location3D with record
      -- A unique waypoint number
      Number : Int64 := 0;
      -- The index of the next waypoint in the list. Consecutively numbered waypoints are <b>not</b> considered linked, the link must be explicitly stated in this field.
      NextWaypoint : Int64 := 0;
      -- Commanded speed for this waypoint. See SpeedType for defintion of this field.
      Speed : Real32 := 0.0;
      -- Type of commanded speed
      SpeedType : SpeedTypeEnum := Airspeed;
      -- The commanded climb rate. Positive values upwards. For surface (ground and sea) entities, this value is ignored.
      ClimbRate : Real32 := 0.0;
      -- The type of turn to execute
      TurnType : TurnTypeEnum := TurnShort;
      -- A list of actions to perform at this waypoint
      VehicleActionList : VA_Seq;
      -- A waypoint for contingency (e.g. lost-comm, alternate mission) operations. A value of zero denotes that no contingency point is specified.
      ContingencyWaypointA : Int64 := 0;
      -- A waypoint for contingency (e.g. lost-comm, alternate mission) operations. A value of zero denotes that no contingency point is specified.
      ContingencyWaypointB : Int64 := 0;
      -- A list of tasks that are associated with this waypoint. A length of zero denotes no associated tasks. This field is for analysis purposes. The automation service should associate a list of tasks with each waypoint to enable analysis of the allocation of tasks to vehicles.
      AssociatedTasks : Int64_Seq;
   end record;

   package WP_Sequences is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Waypoint);
   type WP_Seq is new WP_Sequences.Sequence;

   type KeyValuePair is record
      -- A key (name) for the property
      Key : Unbounded_String := To_Unbounded_String("");
      -- A value for the property
      Value : Unbounded_String := To_Unbounded_String("");
   end record;

   package KVP_Sequences is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => KeyValuePair);
   type KVP_Seq is new KVP_Sequences.Sequence;

   type RoutePlan is record
      -- ID denoting this plan corresponding with requested route constraint pair
      RouteID : Int64 := 0;
      -- Waypoints that connect the start location with the end location. Empty if only costs were requested
      Waypoints : WP_Seq;
      -- Time cost of route. If less than zero, a planning error has occurred
      RouteCost : Int64 := -1;
      -- Error messages, if applicable
      RouteError : KVP_Seq;
   end record;

   package RP_Sequences is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => RoutePlan);
   type RP_Seq is new RP_Sequences.Sequence with
     Predicate =>
       (for all I in 1 .. RP_Sequences.Last (RP_Sequences.Sequence (RP_Seq)) =>
          (for all J in 1 .. RP_Sequences.Last (RP_Sequences.Sequence (RP_Seq)) =>
               I = J or else RP_Sequences.Get (RP_Sequences.Sequence (RP_Seq), I).RouteID /=
               RP_Sequences.Get (RP_Sequences.Sequence (RP_Seq), J).RouteID));
   --  Sequence of route plans have no duplicates

   function Contains (S : RP_Seq; Id : Int64) return Boolean is
     (for some RP of S => RP.RouteID = Id);

   type RouteRequest is new Message_Root with record
      RequestID         : Int64;
      AssociatedTaskID  : Int64;
      VehicleID         : Int64_Seq;
      OperatingRegion   : Int64;
      IsCostOnlyRequest : Boolean;
      RouteRequests     : RC_Seq;
   end record;

   type RoutePlanRequest is new Message_Root with record
      RequestID         : Int64;
      AssociatedTaskID  : Int64;
      VehicleID         : Int64;
      OperatingRegion   : Int64;
      IsCostOnlyRequest : Boolean;
      RouteRequests     : RC_Seq;
   end record;

   type RoutePlanResponse is new Message_Root with record
      ResponseID       : Int64 := 0;
      -- Associated Task ID (0 if no associated task) that this set of responses corresponds to
      AssociatedTaskID : Int64 := 0;
      -- Vehicle that was considered during planning
      VehicleID        : Int64 := 0;
      -- Operating region that was considered during planning
      OperatingRegion  : Int64 := 0;
      -- List of all responses for this vehicle + operating region situation
      RouteResponses   : RP_Seq;
   end record;

   package RPR_Sequences is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => RoutePlanResponse);
   type RPR_Seq is new RPR_Sequences.Sequence;

   type RouteResponse is new Message_Root with record
      -- Response ID matching ID from request ({@link RouteRequest})
      ResponseID : Int64 := 0;
      -- Corresponding route responses for all requested vehicles
      Routes     : RPR_Seq;
   end record;

end Route_Aggregator_Messages;

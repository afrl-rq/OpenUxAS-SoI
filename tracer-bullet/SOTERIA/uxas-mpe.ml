(* File: UxAS-mpe.ml *)

let library =
[ 	{name         = "Validator";
     faults       = ["uedPlannedRoute"];
     input_flows  = ["tasks";"ROZs";"numVehicles"];
     basic_events = ["computationFlt"];
     event_info   = [(0.01, 1.0)];
     output_flows = ["val-tasks"]; 
     formulas     = [FM(("val-tasks", "uedPlannedRoute"), Or[F("tasks");F("ROZs");F("numVehicles");F("computationFlt")])]};

 	{name         = "TaskProcessor4";
     faults       = ["uedPlannedRoute"];
     input_flows  = ["val-tasks"];
     basic_events = ["computationFlt"];
     event_info   = [(0.01, 1.0)];
     output_flows = ["opt1";"opt2";"opt3";"opt4"]; 
     formulas     = [FM(("opt1", "uedPlannedRoute"), Or[F("val-tasks");F("computationFlt")]);
     				 FM(("opt2", "uedPlannedRoute"), Or[F("val-tasks");F("computationFlt")]);
     				 FM(("opt3", "uedPlannedRoute"), Or[F("val-tasks");F("computationFlt")]);
     				 FM(("opt4", "uedPlannedRoute"), Or[F("val-tasks");F("computationFlt")])]};
     
 	{name         = "Aggregator4";
     faults       = ["uedPlannedRoute"];
     input_flows  = ["opt1";"opt2";"opt3";"opt4"];
     basic_events = ["computationFlt"];
     event_info   = [(0.01, 1.0)];
     output_flows = ["blankMatrix"]; 
     formulas     = [FM(("blankMatrix", "uedPlannedRoute"), Or[F("opt1");F("opt2");F("opt3");F("opt4");F("computationFlt")])]};

 	{name         = "Vehicle";
     faults       = ["uedPlannedRoute"];
     input_flows  = ["GPS";"Comm"];
     basic_events = [];
     event_info   = [];
     output_flows = ["vehiclePos"]; 
     formulas     = [FM(("vehiclePos", "uedPlannedRoute"), Or[F("GPS");F("Comm")])]};

 	{name         = "Planner";
     faults       = ["uedPlannedRoute"];
     input_flows  = ["blankMatrix";"vehiclePos1";"vehiclePos2"];
     basic_events = ["rt1_compflt";"rt2_compflt";"rt3_compflt";"rt4_compflt"];
     event_info   = [(0.01, 1.0);(0.01, 1.0);(0.01, 1.0);(0.01, 1.0)];
     output_flows = ["route_cost1";"route_cost2";"route_cost3";"route_cost4";]; 
     formulas     = [FM(("route_cost1", "uedPlannedRoute"), Or[F("blankMatrix");F("vehiclePos1");F("rt1_compflt")]);
    				 FM(("route_cost2", "uedPlannedRoute"), Or[F("blankMatrix");F("vehiclePos1");F("rt2_compflt")]);
    				 FM(("route_cost3", "uedPlannedRoute"), Or[F("blankMatrix");F("vehiclePos2");F("rt3_compflt")]);
    				 FM(("route_cost4", "uedPlannedRoute"), Or[F("blankMatrix");F("vehiclePos2");F("rt4_compflt")])]};

 	{name         = "Aggregator-Collector";
     faults       = ["uedPlannedRoute"];
     input_flows  = ["rt_cost1";"rt_cost2";"rt_cost3";"rt_cost4"];
     basic_events = ["computationFlt"];
     event_info   = [(0.01, 1.0)];
     output_flows = ["FilledMatrix"]; 
     formulas     = [FM(("FilledMatrix", "uedPlannedRoute"), Or[F("rt_cost1");F("rt_cost2");F("rt_cost3");F("rt_cost4");F("computationFlt")])]};

 	{name         = "Picker";
     faults       = ["uedPlannedRoute"];
     input_flows  = ["Matrix"];
     basic_events = ["computationFlt"];
     event_info   = [(0.01, 1.0)];
     output_flows = ["PlannedRoute"]; 
     formulas     = [FM(("PlannedRoute", "uedPlannedRoute"), Or[F("Matrix");F("computationFlt")])]};

 	{name         = "GPS";
     faults       = ["uedPlannedRoute"];
     input_flows  = [];
     basic_events = ["gpsFlt"];
     event_info   = [(0.01, 1.0)];
     output_flows = ["out"]; 
     formulas     = [FM(("out", "uedPlannedRoute"), F("gpsFlt"))]};

 	{name         = "Comm";
     faults       = ["uedPlannedRoute"];
     input_flows  = [];
     basic_events = ["commFlt"];
     event_info   = [(0.01, 1.0)];
     output_flows = ["out"]; 
     formulas     = [FM(("out", "uedPlannedRoute"), F("commFlt"))]};

 	{name         = "UserInput";
     faults       = ["uedPlannedRoute"];
     input_flows  = [];
     basic_events = ["userInpErr"];
     event_info   = [(0.5, 1.0)];
     output_flows = ["out"]; 
     formulas     = [FM(("out", "uedPlannedRoute"), F("userInpErr"))]};
];;

(* ----- CHECK LIBRARY ----- *)
checkLibrary_componentUnique library;;
checkLibrary_nonEmptyFaults library;;
checkLibrary_disjointInputFlowsandBasicEvents library;;
checkLibrary_listsAreConsistentLengths library;;
checkLibrary_allOutputFaultsHaveFormulas library;;
checkLibrary_formulasMakeSense library;;
checkLibrary_aliasesMakeSense library;;

(* -------------------------------------- *)

(* -- ued of Planned Route -- *)
let invalidRoute =
  { instances =
      [makeInstance "validator" "Validator" ();
       makeInstance "userInp_ROZ" "UserInput" ();
       makeInstance "userInp_tasks" "UserInput" ();
       makeInstance "userInp_numVeh" "UserInput" ();
       makeInstance "taskProcessor" "TaskProcessor4" (); 
       makeInstance "aggregator" "Aggregator4" (); 
       makeInstance "vehicle1" "Vehicle" (); 
       makeInstance "vehicle2" "Vehicle" (); 
       makeInstance "gps" "GPS" ();
       makeInstance "comm" "Comm" ();
       makeInstance "planner" "Planner" ();
       makeInstance "aggregator-collector" "Aggregator-Collector" ();
       makeInstance "picker" "Picker" ();
      ];
    connections =
      [ (("validator", "tasks"), ("userInp_tasks", "out"));
		(("validator", "ROZs"), ("userInp_ROZ", "out"));
		(("validator", "numVehicles"), ("userInp_numVeh", "out"));
		(("taskProcessor", "val-tasks"), ("validator", "val-tasks"));
		(("aggregator", "opt1"), ("taskProcessor", "opt1"));
		(("aggregator", "opt2"), ("taskProcessor", "opt2"));
		(("aggregator", "opt3"), ("taskProcessor", "opt3"));
		(("aggregator", "opt4"), ("taskProcessor", "opt4"));
		(("planner", "vehiclePos1"), ("vehicle1", "vehiclePos"));
		(("planner", "vehiclePos2"), ("vehicle2", "vehiclePos"));
		(("planner", "blankMatrix"), ("aggregator", "blankMatrix"));
		(("vehicle1", "GPS"), ("gps", "out"));
		(("vehicle1", "Comm"), ("comm", "out"));
		(("vehicle2", "GPS"), ("gps", "out"));
		(("vehicle2", "Comm"), ("comm", "out"));
		(("aggregator-collector", "rt_cost1"), ("planner", "route_cost1"));
		(("aggregator-collector", "rt_cost2"), ("planner", "route_cost2"));
		(("aggregator-collector", "rt_cost3"), ("planner", "route_cost3"));
		(("aggregator-collector", "rt_cost4"), ("planner", "route_cost4"));
		(("picker", "Matrix"), ("aggregator-collector", "FilledMatrix"));
      ];
    top_fault = ("picker", ("PlannedRoute", "uedPlannedRoute"))
  } ;;

(* ----- CHECK MODEL ----- *)
checkModel_instanceNameUnique invalidRoute;;
checkModel_cnameInstanceIsDefinedInLibrary invalidRoute library;;
checkModel_exposureOfBasicIsDefinedInLibrary invalidRoute library;;
checkModel_validConnections invalidRoute library;;
checkModel_inputFlowUnique invalidRoute;;

(* ----- VISUALIZE ----- *)
dot_gen_show_funct_file library invalidRoute "invalidRoute_mf.gv";;
dot_gen_show_fault_file library invalidRoute "invalidRoute_mflt.gv";;
(* ----- ANALYSIS ----- *)
let invalidRoute_ftree = model_to_ftree library invalidRoute ;;
probErrorCut invalidRoute_ftree;;

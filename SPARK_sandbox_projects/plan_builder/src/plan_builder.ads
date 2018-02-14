-- PlanBuilderService -----------------

with PB_Data_Types;
with PB_Constants;

package plan_builder with SPARK_Mode is

  -- State ----------------------------
  pb_state : PB_Data_Types.state_type;
  pb_pre_state : PB_Data_Types.state_type;


  pb_pre_input_msg : PB_Data_Types.input_message_type;
  pb_pre_output_msg : PB_Data_Types.output_message_type;

--      -- To assist with analysis, it will be useful to record the previous values
--    -- of certain state elements.
--    s_pre_direction : DPSS_Data_Types.direction_type;
--    s_pre_pos       : DPSS_Data_Types.position_type;
--    s_pre_time      : DPSS_Data_Types.time_type;

  cached_unique_automation_request_id : Positive;
  cached_task_implmentation_request_id : Positive;

--  Note: unbounded allowing for cases where 0 tasks need to be serviced
  all_tasks_serviced : Boolean;
  current_total_tasks_to_service : Natural;
  current_serviced_tasks_counter : Natrual;

  -- ----------------------------------

  -- ----------------------------------
  -- State "eq"
  --eq idle_to_idle_waiting : bool = (false ->
  --	(previous_state = IDLE and pre(event(UniqueAutomationRequest_in))));
  function idle_to_idle_waiting return Boolean is
    (pb_pre_state = IDLE and pb_pre_input_msg.msg = UniqueAutomationRequest_in);

--    eq idle_waiting_to_busy_requesting : bool = (false ->
--          		(previous_state = IDLE_WAITING and
--          		pre(event(TaskAssignmentSummary_in)) and
--          		pre(TaskAssignmentSummary_in.CorrespondingAutomationRequestID = cached_unique_automation_request_id)));
--
  function idle_waiting_to_busy_requesting return Boolean is
      (pb_pre_state = IDLE_WAITING and pb_pre_input_msg.msg = TaskAssignmentSummary_in
       and  pb_pre_input_msg.CorrespondingAutomationRequestID = cached_unique_automation_request_id);

--          	eq busy_requesting_to_busy_waiting : bool = (false ->
--          		(previous_state = BUSY_REQUESTING  and
--          			pre(event(TaskImplementationRequest_out))));
--
   function busy_requesting_to_busy_waiting return Boolean is
     (pb_pre_state = BUSY_REQUESTING and pb_pre_output_msg.msg = TaskImplementationRequest_out);


--          	eq busy_waiting_to_busy_requesting : bool = (false->
--          		(previous_state = BUSY_WAITING and
--          		 	pre(event(TaskImplementationResponse_in)) and
--          		 	pre(TaskImplementationResponse_in.ResponseID = cached_task_implmentation_request_id)));

   function busy_waiting_to_busy_requesting return Boolean is
     (pb_pre_state = BUSY_WAITING and pb_pre_input_msg.msg = TaskImplementationResponse_in
      and pb_pre_input_msg.ResponseID = cached_task_implmentation_request_id) ;

--
--          	--[Implied and Altered Spec]: Once a unique automation response is made, transition to IDLE.
--          	eq busy_requesting_to_idle : bool = (false ->
--          		(previous_state = BUSY_REQUESTING and
--          		pre(event(UniqueAutomationResponse_out)) and
--          		pre(UniqueAutomationResponse_out.ResponseID = cached_unique_automation_request_id)));

   function busy_requesting_to_idle return Boolean is
      (pb_pre_state = BUSY_REQUESTING and pb_pre_output_msg.msg = UniqueAutomationResponse_out
       and pb_pre_output_msg.CorrespondingAutomationRequestID = cached_unique_automation_request_id);

   function some_transition return Boolean is
      (idle_to_idle_waiting'Output or
       idle_waiting_to_busy_requesting'Output or
       busy_requesting_to_busy_waiting'Output or
       busy_waiting_to_busy_requesting'Output or
       busy_requesting_to_idle'Output);

  -- ------------------------------------------------------------------------ --


--  LIKELY PRECONDITION ---
--  TODO: is there a way to remove this assumption and place it in the parent system?
--  The purpose of this assumption is to ensure it is OK to use MAX_TASKS as an upper bound.
--  assume "TaskAssignmentSummary_in must provide a TaskList of size greater than 0 and less than or equal to 10":
--    event(TaskAssignmentSummary_in) =>
--          TaskAssignmentSummary_in.TaskListSize > 0 and TaskAssignmentSummary_in.TaskListSize <= MAX_TASKS;
--
--  TODO: is there a way to get total tasks from the TaskAssignmentSummary array directly?
--


   procedure initialize_pb
   with
     Global => (Output => (all_tasks_serviced,
                           current_total_tasks_to_service,
                           current_serviced_tasks_counter,
                           pb_state,
                           pb_pre_state)),
     Post => (
       all_tasks_serviced = True and
       current_total_tasks_to_service = 0 and
       current_serviced_tasks_counter = 0 and

       --  guarantee "The PlanBuilderService begins in the IDLE state" :
       --    (state =IDLE)->true;
       pb_state = IDLE and
       pb_pre_state = IDLE
     );

  -- ------------------------------------------------------------------------ --
  -- Guarantees

--  guarantee "Self loops": not some_transition => (state = previous_state);
   function self_loops return Booolean
   is
     (pb_state = (
        if not some_transition then
          pb_pre_state));


--   	--Similar to both the�RouteAggregator�and the�AssignmentTreeBranchBoundService,
--     	--the�PlanBuilderService�utilizes a received UniqueAutomationRequest�to detect
--     	--that a new mission request has been made to the system. The UniqueAutomationRequest�is stored ...
--     	guarantee "The latest automation request ID is cached when in the IDLE state, otherwise
--     		the cached request ID does not change" :
--     		if (state = IDLE and event(UniqueAutomationRequest_in))  then
--     			cached_unique_automation_request_id = UniqueAutomationRequest_in.RequestID
--     		else
--     		--TODO: ASK DEREK: Assuming ignoring requests in all other cases (keep previous cached request constant)
--     			(cached_unique_automation_request_id = pre(cached_unique_automation_request_id));
   function cachedRequestID return Boolean
   is
     (cached_unique_automation_request_id = (
       if (pb_pre_state = IDLE and
           pb_pre_input_msg.msg = PB_Data_Types.in_message_type.UniqueAutomationRequest_in) then
         pb_pre_input_msg.id));
--     else
       -- The cached_unique_automation_request_id is not changed.




--          	guarantee "[ADDED STATE] Transition to IDLE_WAITING after a unique automation request is received" :
--          		idle_to_idle_waiting =>
--          			(state = IDLE_WAITING);





--          	guarantee "The UniqueAutomationRequest is stored until a TaskAssignmentSummary that corresponds
--          		to the unique ID is received. At this point, the PlanBuilderService transitions from the idle 
--          		state to the busy [requesting] state.":
--          		idle_waiting_to_busy_requesting =>
--          			((state = BUSY_REQUESTING) and
--          			(current_total_tasks_to_service = pre(TaskAssignmentSummary_in.TaskListSize)) and
--          			current_serviced_tasks_counter = 0);





--          	guarantee "[Added Guarantee] When not transitioning to BUSY_REQUESTING the internal caching variables
--          		current_total_task_to_service and cached_unique_automation_request_id remain constant" :
--          		not idle_waiting_to_busy_requesting =>
--          			(current_total_tasks_to_service = pre(current_total_tasks_to_service));





--          	guarantee "[In the BUSY REQUESTING state] Using the list of ordered Tasks dictated by the TaskAssignmentSummary, the PlanBuilderService sends
--          		a TaskImplementationRequest to each Task in order and waits for a TaskImplementationResponse from each Task 
--          		before moving to the next. " :
--          			if (state = BUSY_REQUESTING and not all_tasks_serviced) then
--          				event(TaskImplementationRequest_out) and
--          				cached_task_implmentation_request_id = TaskImplementationRequest_out.RequestID
--          			else
--          				(not event(TaskImplementationRequest_out)) and
--          				(cached_task_implmentation_request_id = pre(cached_task_implmentation_request_id));





end plan_builder;

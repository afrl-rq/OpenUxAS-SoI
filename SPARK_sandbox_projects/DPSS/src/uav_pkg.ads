-- -------------------------------------------------------------------------- --
-- UAV_Pkg.ads                  Dependable Computing

with DPSS_Data_Types;
with DPSS_Constants;

package UAV_Pkg with SPARK_Mode is

  -- ------------------------------------------------------------------------ --
  -- State
  --
  -- NOTE: id has been elevated to a state variable, so that it can be
  -- separately set via an initialization procedure.
  s_id : Integer;

  -- Record if the component has been initialized.
  s_initialized : Boolean := False;


  -- These are "true" state elements.
  s_direction : DPSS_Data_Types.direction_type;
  s_pos       : DPSS_Data_Types.position_type;

  -- This is built into AGREE, we add this explicitly in SPARK. Note that time
  -- is only required because the vehicle does its own position update. If
  -- position were updated externally (were an input to the vehicle controller)
  -- then we could completely eliminate time.
  s_time : DPSS_Data_Types.time_type;


  -- To assist with analysis, it will be useful to record the previous values
  -- of certain state elements.
  s_pre_direction : DPSS_Data_Types.direction_type;
  s_pre_pos       : DPSS_Data_Types.position_type;
  s_pre_time      : DPSS_Data_Types.time_type;


  -- ------------------------------------------------------------------------ --
  -- State "eq"
  --
  -- NOTE: in AGREE, these are definitions of equations that can be accessed
  -- through a single variable name. We use expression functions to serve this
  -- purpose.

  --Shared border positions

  -- eq S_L : DPSS_Data_Types::Position_Type =
  --   real(id-1)*DPSS_Constants.P_GLOBAL/DPSS_Constants.N_real;
  function S_L return DPSS_Data_Types.position_type is
    (Float(s_id-1)*DPSS_Constants.P_GLOBAL/DPSS_Constants.N_real);

  -- eq S_R : DPSS_Data_Types::Position_Type =
  --   real(id)*DPSS_Constants.P_GLOBAL/DPSS_Constants.N_real;
  function S_R return DPSS_Data_Types.position_type is
    (Float(s_id)*DPSS_Constants.P_GLOBAL/DPSS_Constants.N_real);

  --Previous direction
  -- eq pre_direction : DPSS_Data_Types::Direction_Type =
  --   prev(direction, suggested_initial_direction);
  --
  -- NOTE: it's not entirely clear what the best way is to model the use of the
  -- prev operator in AGREE. Generally, the prev operator is used to describe,
  -- in a constraint that is updating the value of an output, how the new value
  -- should be computed: instead of calling the new value "next," we refer to
  -- the current value as prev.
  --
  -- Since we're doing this implementation in SPARK, we get that kind of update
  -- behavior "automatically" - but we do need to be able to talk about how
  -- the updates take place, so that we can prove our constraints.
  --f
  -- For now, we are modeling the prev by carrying around an explicit state
  -- variable that records the prior value. We check this update on the
  -- postcondition of run using 'Old.
  --
  -- The initialization behavior of the prev operator is handled through the
  -- postcondition on the initialization procedure.
  function pre_direction return DPSS_Data_Types.direction_type is
    (s_pre_direction);

  --Previous position
  -- eq pre_pos : DPSS_Data_Types::Position_Type =
  --   prev(pos, initial_position);
  --
  -- NOTE: see comment above on pre_direction
  function pre_pos return DPSS_Data_Types.position_type is
    (s_pre_pos);

  --These Booleans are true iff the neighbors meet (i.e., are co-located) on
  -- this timestep.
  -- eq meet_LN : bool = (pos_LN = pos); --Meet left neighbor?
  --
  -- NOTE: this is problematic, as pos_LN is an input to the component and so
  -- is not actually in scope at this point. We therefore make pos_LN an input.
  -- We also make pos an input, for completeness.
  function meet_LN(pos_LN : DPSS_Data_Types.position_type;
                   pos    : DPSS_Data_Types.position_type) return Boolean
  is
    (pos_LN = pos);

  -- eq meet_RN : bool = (pos_RN = pos); --Meet right neighbor?
  function meet_RN(pos_RN : DPSS_Data_Types.position_type;
                   pos    : DPSS_Data_Types.position_type) return Boolean
  is
    (pos_RN = pos);


  -- ------------------------------------------------------------------------ --
  -- Component Initialization

  procedure initialize_component(
    suggested_initial_direction : in DPSS_Data_Types.direction_type;
    initial_position            : in DPSS_Data_Types.position_type;
    id                          : in Integer)
  with
    Global => (Output => (s_direction,
                          s_pos,
                          s_id,

                          s_pre_direction,
                          s_pre_pos,

                          s_time,
                          s_pre_time,

                          s_initialized)),

    Pre => (
      -- assume "ID in range":
      --     id >= 1 and id <= DPSS_Constants.N_int;
      (id >= 1 and id <= DPSS_Constants.N_int) and

      -- assume "ID is fixed":
      --     true -> (id = pre(id));
      --
      -- NOTE: this assumption handled by use of separate initialization
      -- procedure.

      -- assume "Input initial position is between 0 and P_GLOBAL":
      --     (0.0 <= initial_position
      --     and initial_position <= DPSS_Constants.P_GLOBAL)
      --     -> true;
      --
      -- NOTE: Arrow operator semantics handled through use of separate
      -- initialization procedure.
      (0.0 <= initial_position and initial_position <= DPSS_Constants.P_GLOBAL) and

      -- assume "Suggested initial direction is LEFT or RIGHT":
      --     (suggested_initial_direction = DPSS_Constants.LEFT
      --        or suggested_initial_direction = DPSS_Constants.RIGHT)
      --     -> true;
      (suggested_initial_direction = DPSS_Constants.LEFT or
       suggested_initial_direction = DPSS_Constants.RIGHT)
    ),

    Post => (
      s_id = id and

      s_direction = suggested_initial_direction and
      s_pre_direction = suggested_initial_direction and

      s_pos = initial_position and
      s_pre_pos = initial_position and

      s_initialized and

      s_time = 0.0 and
      s_pre_time = 0.0
    );

  -- ------------------------------------------------------------------------ --
  -- Guarantees
  --
  -- We encode guarantees as predicates expression functions that we then assert
  -- in the postcondition of the run procedure.

  -- guarantee "Direction formula":
  function direction_formula(
    pos_LN : DPSS_Data_Types.position_type;
    pos_RN : DPSS_Data_Types.position_type) return Boolean
  is
    (s_direction = (
       -- Turn around at the left boundary
       if s_pos <= 0.0 then
         1

       -- Turn around at the right boundary
       elsif s_pos >= DPSS_Constants.P_GLOBAL then
         -1

       -- If meeting left neighbor, travel together to shared border
       elsif meet_LN(pos_LN, s_pos) then
         (if s_pos <= S_L then
            1
          else --pos > S_L
            -1
         )

       -- Else if meeting right neighbor, travel together to shared border
       elsif meet_RN(pos_RN, s_pos) then
         (if s_pos < S_R then
            1
          else --pos >= S_R
            -1
         )

       -- In all other cases, proceed in the same direction
       else
         pre_direction
    ));

  -- guarantee "Goal formula":
  --
  -- We do not need the goal to be state, since we never access its prior value.
  -- So we pass in the goal as a parameter to this function, allowing us to use
  -- it to check the goal output in run.
  function goal_formula(
    pos_LN : DPSS_Data_Types.position_type;
    pos_RN : DPSS_Data_Types.position_type;
    goal   : DPSS_Data_Types.position_type) return Boolean
  is
    (goal = (
       -- If co-located with left neighbor,...
       if meet_LN(pos_LN, s_pos) then
         --...and at or to the left of the shared border, make goal the right endpoint
         (if s_pos <= S_L then
            DPSS_Constants.P_GLOBAL

          --...and to the right of the shared border, make goal the shared border
          else -- pos > S_L
            S_L
         )

       -- Else if co-located with right neighbor,...
       elsif meet_RN(pos_RN, s_pos) then
         --...and at or to the right of the shared border, make goal the left endpoint
         (if s_pos >= S_R then
            0.0

          --...and to the left of the shared border, make goal the shared border
          else -- pos < S_R
            S_R
          )

       -- Else if heading right, set goal to the right endpoint
       elsif s_direction = 1 then
         DPSS_Constants.P_GLOBAL

       -- Else if heading left, set goal to the left endpoint
       else --direction = -1
         0.0
    ));


  -- guarantee "Position formula":
  --
  -- NOTE: encoding of -> operator handled by setting the initial position
  -- during initialization.
  function position_formula return Boolean is
    (s_pos = (
       if pre_direction = 1 then
         pre_pos + DPSS_Constants.V*(s_time - s_pre_time)
       else --pre_direction = -1
         pre_pos - DPSS_Constants.V*(s_time - s_pre_time)
    ));

  -- ------------------------------------------------------------------------ --
  -- Component State Update

  procedure run_component(
    pos_LN : in DPSS_Data_Types.position_type;
    pos_RN : in DPSS_Data_Types.position_type;

    time : in DPSS_Data_Types.time_type;

    direction : out DPSS_Data_Types.direction_type;
    goal      : out DPSS_Data_Types.position_type;
    pos       : out DPSS_Data_Types.position_type)
  with
    Global => (Input  => (s_id,
                          s_initialized),

               In_Out => (s_direction,
                          s_pos,
                          s_time,
                          s_pre_time),

               Output => (s_pre_direction,
                          s_pre_pos)),

    Pre => (
      s_initialized and
      time > s_pre_time and

      -- This is set up in the initialization and then maintained in the
      -- postcondition for run.
      (s_direction = -1 or s_direction = 1)
    ),

    Post => (
      -- Ensure that we are updating our _pre variables correctly
      s_pre_direction = s_direction'Old and
      s_pre_pos = s_pos'Old and
      s_pre_time = s_time'Old and

      -- Ensure that we update state correctly
      direction_formula(pos_LN, pos_RN) and
      position_formula and
      s_time = time and

      -- Ensure that we set the outputs correct
      s_direction = direction and
      goal_formula(pos_LN, pos_RN, goal) and
      s_pos = pos and

      -- Maintain correct handling of the direction variable, to set up
      -- for the next invocation of run.
      (direction = -1 or direction = 1)
    );
end UAV_Pkg;

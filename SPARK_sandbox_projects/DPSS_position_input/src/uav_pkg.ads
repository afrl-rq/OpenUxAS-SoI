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

  -- The direction the vehicle is traveling.
  s_direction : DPSS_Data_Types.direction_type;

  -- The direction the vehicle was traveling previously. This state element,
  -- which was accessed with the prev operator in AGREE, is used in the
  -- implementation of the component and so is a true element of state.
  s_pre_direction : DPSS_Data_Types.direction_type;


  -- ------------------------------------------------------------------------ --
  -- Ghost State

  -- In order to be able to reason about how position changes over time with
  -- respect to direction, we need a record of the prior value of position.
  -- In AGREE, this can be done with the prev operator. In SPARK, we don't have
  -- an operator that can do that, and the 'Old attribute is not available
  -- across subprogram calls.
  --
  -- Since this variable is only needed for analysis, we mark it Ghost.
  ghost_pre_position : DPSS_Data_Types.position_type with Ghost;

  -- We want to be sure that the run_component procedure is not called before
  -- the component is initialized, so we record initialization with a variable.
  --
  -- Since we check this variable in the precondition but _not_ in the procedure
  -- body, we mark it ghost.
  ghost_initialized : Boolean := False with Ghost ;


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
    (Float(s_id-1)*DPSS_Constants.P_GLOBAL/DPSS_Constants.N_real)
  with
    Pre => (s_id >= 1 and s_id <= DPSS_Constants.N_int);

  -- eq S_R : DPSS_Data_Types::Position_Type =
  --   real(id)*DPSS_Constants.P_GLOBAL/DPSS_Constants.N_real;
  function S_R return DPSS_Data_Types.position_type is
    (Float(s_id)*DPSS_Constants.P_GLOBAL/DPSS_Constants.N_real)
  with
    Pre => (s_id >= 1 and s_id <= DPSS_Constants.N_int);


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
  --
  -- For now, we are modeling the prev by carrying around an explicit state
  -- variable that records the prior value. We check this update on the
  -- postcondition of run using 'Old.
  --
  -- The initialization behavior of the prev operator is handled through the
  -- postcondition on the initialization procedure.
  --
  -- This is only used in the guarantees, so I have marked it as Ghost
  function pre_direction return DPSS_Data_Types.direction_type is
    (s_pre_direction)
  with Ghost;

  --These Booleans are true iff the neighbors meet (i.e., are co-located) on
  -- this timestep.
  -- eq meet_LN : bool = (pos_LN = pos); --Meet left neighbor?
  --
  -- NOTE: this is problematic, as pos_LN is an input to the component and so
  -- is not actually in scope at this point. We therefore make pos_LN an input.
  -- We also make pos an input, for completeness.
  function meet_LN(position_LN : DPSS_Data_Types.position_type;
                   position    : DPSS_Data_Types.position_type) return Boolean
  is
    (position_LN = position);

  -- eq meet_RN : bool = (pos_RN = pos); --Meet right neighbor?
  function meet_RN(position_RN : DPSS_Data_Types.position_type;
                   position    : DPSS_Data_Types.position_type) return Boolean
  is
    (position_RN = position);


  -- ------------------------------------------------------------------------ --
  -- Component Initializatoin

  procedure initialize_component(
    suggested_initial_direction : in DPSS_Data_Types.direction_type;
    initial_position            : in DPSS_Data_Types.position_type;
    id                          : in Integer)
  with
    Global => (Output => (s_id,
                          s_direction,
                          s_pre_direction,

                          ghost_pre_position,
                          ghost_initialized)),

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
      (0.0 <= initial_position and
              initial_position <= DPSS_Constants.P_GLOBAL) and

      -- assume "Suggested initial direction is LEFT or RIGHT":
      --     (suggested_initial_direction = DPSS_Constants.LEFT
      --        or suggested_initial_direction = DPSS_Constants.RIGHT)
      --     -> true;
      --
      -- NOTE: Arrow operator semantics handled through use of separate
      -- initialization procedure.
      (suggested_initial_direction = DPSS_Constants.LEFT or
       suggested_initial_direction = DPSS_Constants.RIGHT)
    ),

    Post => (
      s_id = id and

      s_direction = suggested_initial_direction and
      s_pre_direction = suggested_initial_direction and

      ghost_pre_position = initial_position and
      ghost_initialized
    );

  -- ------------------------------------------------------------------------ --
  -- Guarantees
  --
  -- We encode guarantees as predicates expression functions that we then assert
  -- in the postcondition of the run procedure.
  --
  -- These guarantees are not for execution, so they are marked as Ghost.

  -- guarantee "Direction formula":
  function direction_formula(
    position: DPSS_Data_Types.position_type;
    position_LN : DPSS_Data_Types.position_type;
    position_RN : DPSS_Data_Types.position_type) return Boolean
  is
    (s_direction = (
       -- Turn around at the left boundary
       if position <= 0.0 then
         1

       -- Turn around at the right boundary
       elsif position >= DPSS_Constants.P_GLOBAL then
         -1

       -- If meeting left neighbor, travel together to shared border
       elsif meet_LN(position_LN, position) then
         (if position <= S_L then
            1
          else --pos > S_L
            -1
         )

       -- Else if meeting right neighbor, travel together to shared border
       elsif meet_RN(position_RN, position) then
         (if position < S_R then
            1
          else --pos >= S_R
            -1
         )

       -- In all other cases, proceed in the same direction
       else
         pre_direction
    ))
  with
    Ghost,
    Pre => (s_id >= 1 and s_id <= DPSS_Constants.N_int);

  -- guarantee "Goal formula":
  --
  -- We do not need the goal to be state, since we never access its prior value.
  -- So we pass in the goal as a parameter to this function, allowing us to use
  -- it to check the goal output in run.
  function goal_formula(
    position    : DPSS_Data_Types.position_type;
    position_LN : DPSS_Data_Types.position_type;
    position_RN : DPSS_Data_Types.position_type;
    goal   : DPSS_Data_Types.position_type) return Boolean
  is
    (goal = (
       -- If co-located with left neighbor,...
       if meet_LN(position_LN, position) then
         --...and at or to the left of the shared border, make goal the right endpoint
         (if position <= S_L then
            DPSS_Constants.P_GLOBAL

          --...and to the right of the shared border, make goal the shared border
          else -- pos > S_L
            S_L
         )

         -- Else if co-located with right neighbor,...
         elsif meet_RN(position_RN, position) then
           --...and at or to the right of the shared border, make goal the left endpoint
           (if position >= S_R then
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
    ))
  with
    Ghost,
    Pre => (s_id >= 1 and s_id <= DPSS_Constants.N_int);


  -- ------------------------------------------------------------------------ --
  -- Component State Update

  procedure run_component(
    position    : in DPSS_Data_Types.position_type;
    position_LN : in DPSS_Data_Types.position_type;
    position_RN : in DPSS_Data_Types.position_type;

    direction : out DPSS_Data_Types.direction_type;
    goal      : out DPSS_Data_Types.position_type)
  with
    Global => (Input  => (s_id,
                          ghost_initialized),

               In_Out => (s_direction,
                          ghost_pre_position),

               Output => (s_pre_direction)),

    Pre => (
      -- The component must be initialized before run can be called.
      ghost_initialized and

      -- This is set up in the initialization and then maintained in the
      -- postcondition for run.
      (s_direction = -1 or s_direction = 1) and

      -- Assume that the position update respects the direction of travel.
      (if s_direction = 1 then
         position > ghost_pre_position
       else
         position < ghost_pre_position) and

      -- With the current type system, this is needed to ensure that S_L and
      -- S_R do not over/underflow. This is set correctly in the initialization
      -- but we need a promise that it will remain correct when this procedure
      -- is called.
      (s_id >= 1 and s_id <= DPSS_Constants.N_int)
    ),

    Post => (
      -- Ensure that we are updating our _pre variables correctly
      s_pre_direction = s_direction'Old and
      ghost_pre_position = position and

      -- Ensure that we update state correctly
      direction_formula(position, position_LN, position_RN) and

      -- Ensure that we set the outputs correctly
      s_direction = direction and
      goal_formula(position, position_LN, position_RN, goal) and

      -- Maintain correct handling of the direction variable, to set up
      -- for the next invocation of run. Implied by the direction formula and
      -- the precondition on s_direction, but set as a separate check, here.
      (s_direction = -1 or s_direction = 1)
    );
end UAV_Pkg;

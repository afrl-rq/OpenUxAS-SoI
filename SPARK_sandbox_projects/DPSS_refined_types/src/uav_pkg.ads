-- -------------------------------------------------------------------------- --
-- UAV_Pkg.ads                  Dependable Computing

with DPSS_Data_Types;
with DPSS_Constants;

package UAV_Pkg with SPARK_Mode is
  -- ------------------------------------------------------------------------ --
  -- Types
  --
  -- I've added a custom subtype here, to represent the UAV id. This eliminates
  -- several preconditions related to the valid range of s_id.
  subtype id_type is Integer range 1 .. DPSS_Constants.N_int;


  -- ------------------------------------------------------------------------ --
  -- State
  --
  -- NOTE: id has been elevated to a state variable, so that it can be
  -- separately set via an initialization procedure.
  s_id : id_type;

  -- The direction the vehicle is traveling.
  s_direction : DPSS_Data_Types.direction_type;

  -- The direction the vehicle was traveling previously. This state element,
  -- which was accessed with the prev operator in AGREE, is used in the
  -- implementation of the component and so is a true element of state.
  s_pre_direction : DPSS_Data_Types.direction_type;


  -- ------------------------------------------------------------------------ --
  -- Ghost State

  -- We want to be sure that the run_component procedure is not called before
  -- the component is initialized, so we record initialization with a variable.
  --
  -- Since we check this variable in the precondition but _not_ in the procedure
  -- body, we mark it ghost.
  ghost_initialized : Boolean := False with Ghost;


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
    (Float(s_id-1)*DPSS_Constants.P_GLOBAL/Float(DPSS_Constants.N_int));

  -- eq S_R : DPSS_Data_Types::Position_Type =
  --   real(id)*DPSS_Constants.P_GLOBAL/DPSS_Constants.N_real;
  function S_R return DPSS_Data_Types.position_type is
    (Float(s_id)*DPSS_Constants.P_GLOBAL/Float(DPSS_Constants.N_int));


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
    id                          : in id_type)
  with
    Global => (In_Out => ghost_initialized,

               Output => (s_id,
                          s_direction,
                          s_pre_direction)),

    Pre => (
      -- assume "ID in range":
      --     id >= 1 and id <= DPSS_Constants.N_int;
      --
      -- NOTE: encoded in type.

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
       suggested_initial_direction = DPSS_Constants.RIGHT) and

      -- Make sure we don't initialize multiple times
      not ghost_initialized
    ),

    Post => (
      s_id = id and

      s_direction = suggested_initial_direction and
      s_pre_direction = suggested_initial_direction and

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
    position    : DPSS_Data_Types.position_type;
    position_LN : DPSS_Data_Types.position_type;
    position_RN : DPSS_Data_Types.position_type) return Boolean
  is
    (s_direction = (
       -- Turn around at the left boundary
       if position <= 0.0 then
         DPSS_Constants.RIGHT

       -- Turn around at the right boundary
       elsif position >= DPSS_Constants.P_GLOBAL then
         DPSS_Constants.LEFT

       -- If meeting left neighbor, travel together to shared border
       elsif meet_LN(position_LN, position) then
         (if position <= S_L then
            DPSS_Constants.RIGHT
          else --pos > S_L
            DPSS_Constants.LEFT
         )

       -- Else if meeting right neighbor, travel together to shared border
       elsif meet_RN(position_RN, position) then
         (if position < S_R then
            DPSS_Constants.RIGHT
          else --pos >= S_R
            DPSS_Constants.LEFT
         )

       -- In all other cases, proceed in the same direction
       else
         s_pre_direction
    ))
  with Ghost;

  -- guarantee "Goal formula":
  --
  -- We do not need the goal to be state, since we never access its prior value.
  -- So we pass in the goal as a parameter to this function, allowing us to use
  -- it to check the goal output in run.
  function goal_formula(
    position    : DPSS_Data_Types.position_type;
    position_LN : DPSS_Data_Types.position_type;
    position_RN : DPSS_Data_Types.position_type;
    goal        : DPSS_Data_Types.position_type) return Boolean
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
          elsif s_direction = DPSS_Constants.RIGHT then
            DPSS_Constants.P_GLOBAL

          -- Else if heading left, set goal to the left endpoint
          else --direction = -1
            0.0
    ))
  with Ghost;


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

               In_Out => s_direction,

               Output => s_pre_direction),

    Pre => (
      -- The component must be initialized before run can be called.
      ghost_initialized
    ),

    Post => (
      -- Ensure that we are updating our _pre variables correctly
      s_pre_direction = s_direction'Old and

      -- Ensure that we update state correctly
      direction_formula(position, position_LN, position_RN) and

      -- Ensure that we set the outputs correctly
      s_direction = direction and
      goal_formula(position, position_LN, position_RN, goal)
    );
end UAV_Pkg;

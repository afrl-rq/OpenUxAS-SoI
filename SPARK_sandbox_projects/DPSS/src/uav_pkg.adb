-- -------------------------------------------------------------------------- --
-- UAV_Pkg.adb                  Dependable Computing

package body UAV_Pkg with SPARK_Mode is

  procedure initialize_component(
    suggested_initial_direction : in DPSS_Data_Types.direction_type;
    initial_position            : in DPSS_Data_Types.position_type;
    id                          : in Integer)
  is begin
    -- Step 1: Initialize _pre state elements
    s_pre_direction := suggested_initial_direction;
    s_pre_pos       := initial_position;
    s_pre_time      := 0.0;

    -- Step 2: Initialize state elements
    s_direction := suggested_initial_direction;
    s_pos       := initial_position;
    s_id        := id;
    s_time      := 0.0;

    -- Step 3: Mark initialization complete
    s_initialized := True;
  end initialize_component;

  procedure run_component(
    pos_LN : in DPSS_Data_Types.position_type;
    pos_RN : in DPSS_Data_Types.position_type;

    time : in DPSS_Data_Types.time_type;

    direction : out DPSS_Data_Types.direction_type;
    goal      : out DPSS_Data_Types.position_type;
    pos       : out DPSS_Data_Types.position_type)
  is
    next_direction : DPSS_Data_Types.direction_type;
    next_position  : DPSS_Data_Types.position_type;
    next_goal      : DPSS_Data_Types.position_type;
    next_time      : DPSS_Data_Types.time_type;
  begin
    -- Step 1: Update _pre state elements
    s_pre_direction := s_direction;
    s_pre_pos       := s_pos;
    s_pre_time      := s_time;

    -- Step 2: Compute next states and outputs

    -- Time goes first
    next_time := time;

    -- Position must go next
    --
    -- NOTE: initially, I tried to do this like this (taking advantage of the
    -- way in which direction is constructed), but could not get the proof to
    -- go through. My guess is that the overflows were preventing the proof
    -- system from concluding that this was right:
    --
    -- next_position := s_pre_pos +
    --                   DPSS_Constants.V*(next_time - s_pre_time)*
    --                     Float(s_pre_direction);
    --
    -- So I've done this in the more straightforward way:
    if s_pre_direction = 1 then
      next_position := s_pre_pos + DPSS_Constants.V*(next_time - s_pre_time);
    else
      next_position := s_pre_pos - DPSS_Constants.V*(next_time - s_pre_time);
    end if;

    pragma Assert(
      if s_pre_direction = 1 then
        next_position = s_pre_pos + DPSS_Constants.V*(next_time - s_pre_time));

    pragma Assert(
      if s_pre_direction = -1 then
        next_position = s_pre_pos - DPSS_Constants.V*(next_time - s_pre_time));

    -- Direction must go next
    if next_position <= 0.0 then
      next_direction := 1;
    elsif next_position >= DPSS_Constants.P_GLOBAL then
      next_direction := -1;
    elsif meet_LN(pos_LN, next_position) then
      if next_position <= S_L then
        next_direction := 1;
      else
        next_direction := -1;
      end if;
    elsif meet_RN(pos_RN, next_position) then
      if next_position < S_R then
        next_direction := 1;
      else
        next_direction := -1;
      end if;
    else
      next_direction := s_pre_direction;
    end if;

    pragma Assert(next_direction = 1 or
                  next_direction = -1);

    -- Goal goes last.
    -- If we meed our left neighbor
    if pos_LN = next_position then
      if next_position <= S_L then
        next_goal := DPSS_Constants.P_GLOBAL;
      else
        next_goal := S_L;
      end if;

    -- otherwise if we meet our right neighbor
    elsif pos_RN = next_position then
      if next_position >= S_R then
        next_goal := 0.0;
      else
        next_goal := S_R;
      end if;

    -- otherwise if direction is positive
    elsif next_direction = 1 then
      next_goal := DPSS_Constants.P_GLOBAL;

    -- otherwise
    else
--      pragma Assert(next_direction = -1);

      next_goal := 0.0;
    end if;

    pragma Assert(next_goal = 0.0 or
                  next_goal = S_L or
                  next_goal = S_R or
                  next_goal = DPSS_Constants.P_GLOBAL);

    pragma Assert(if pos_LN = next_position and
                     next_position <= S_L
                  then
                    next_goal = DPSS_Constants.P_GLOBAL);

    pragma Assert(if pos_LN = next_position and
                     next_position >  S_L
                  then
                    next_goal = S_L);

    pragma Assert(if pos_LN /= next_position and
                     pos_RN  = next_position and
                     next_position >= S_R
                  then
                    next_goal = 0.0);

    pragma Assert(if pos_LN /= next_position and
                     pos_RN  = next_position and
                     next_position <  S_R
                  then
                    next_goal = S_R);

    pragma Assert(if pos_LN /= next_position and
                     pos_RN /= next_position and
                     next_direction = 1
                  then
                    next_goal = DPSS_Constants.P_GLOBAL);

    pragma Assert(if pos_LN /= next_position and
                     pos_RN /= next_position and
                     next_direction /= 1
                  then
                    next_goal = 0.0);


    -- Step 3: Update state elements
    s_direction := next_direction;
    s_pos := next_position;
    s_time := next_time;

    -- Step 4: Set outputs
    direction := s_direction;
    goal := next_goal;
    pos := s_pos;
  end run_component;
end UAV_Pkg;

-- -------------------------------------------------------------------------- --
-- UAV_Pkg.adb                  Dependable Computing

package body UAV_Pkg with SPARK_Mode is

  procedure initialize_component(
    suggested_initial_direction : in DPSS_Data_Types.direction_type;
    initial_position            : in DPSS_Data_Types.position_type;
    id                          : in id_type)
  is begin
    -- Step 1: Initialize _pre state elements
    s_pre_direction    := suggested_initial_direction;

    -- Step 2: Initialize state elements
    s_direction := suggested_initial_direction;
    s_id        := id;

    -- Step 3: Mark initialization complete
    ghost_initialized := True;
  end initialize_component;

  procedure run_component(
    position    : in DPSS_Data_Types.position_type;
    position_LN : in DPSS_Data_Types.position_type;
    position_RN : in DPSS_Data_Types.position_type;

    direction : out DPSS_Data_Types.direction_type;
    goal      : out DPSS_Data_Types.position_type)
  is
    next_direction : DPSS_Data_Types.direction_type;
    next_goal      : DPSS_Data_Types.position_type;
  begin
    -- Step 1: Update _pre state elements
    s_pre_direction    := s_direction;


    -- Step 2: Compute next states and outputs

    -- Direction updates before goal
    if position <= 0.0 then
      next_direction := DPSS_Constants.RIGHT;
    elsif position >= DPSS_Constants.P_GLOBAL then
      next_direction := DPSS_Constants.LEFT;
    elsif meet_LN(position_LN, position) then
      if position <= S_L then
        next_direction := DPSS_Constants.RIGHT;
      else
        next_direction := DPSS_Constants.LEFT;
      end if;
    elsif meet_RN(position_RN, position) then
      if position < S_R then
        next_direction := DPSS_Constants.RIGHT;
      else
        next_direction := DPSS_Constants.LEFT;
      end if;
    else
      next_direction := s_pre_direction;
    end if;

    -- Goal updates last.
    -- If we meed our left neighbor
    if meet_LN(position_LN, position) then
      if position <= S_L then
        next_goal := DPSS_Constants.P_GLOBAL;
      else
        next_goal := S_L;
      end if;

    -- otherwise if we meet our right neighbor
    elsif meet_RN(position_RN, position) then
      if position >= S_R then
        next_goal := 0.0;
      else
        next_goal := S_R;
      end if;

    -- otherwise if direction is positive
    elsif next_direction = DPSS_Constants.RIGHT then
      next_goal := DPSS_Constants.P_GLOBAL;

    -- otherwise
    else
      next_goal := 0.0;
    end if;


    -- Step 3: Update state elements
    s_direction := next_direction;


    -- Step 4: Set outputs
    direction := s_direction;
    goal := next_goal;
  end run_component;
end UAV_Pkg;

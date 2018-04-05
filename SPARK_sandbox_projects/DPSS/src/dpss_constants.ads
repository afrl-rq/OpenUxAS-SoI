-- -------------------------------------------------------------------------- --
-- DPSS_Constants.ads           Dependable Computing

with DPSS_Data_Types;

package DPSS_Constants with SPARK_Mode is

  -- const P_GLOBAL : Base_Types::Float = 10.0;
  P_GLOBAL : constant Float := 10.0;

  -- const V : Base_Types::Float = 1.0; --velocity
  V : constant Float := 1.0;

  -- const Time_to_travel_full_length : DPSS_Data_Types::Time_Type = P_GLOBAL/V;
  Time_to_travel_full_length : constant DPSS_Data_Types.time_type := P_GLOBAL/V;

  -- const LEFT : int = -1;
  LEFT : constant Integer := -1;

  -- const RIGHT : int = 1;
  RIGHT : constant Integer := 1;

  -- const N_int : int = 3; --Number of vehicles
  N_int : constant Integer := 3;

  -- const N_real : real = 3.0; --Number of vehicles
  N_real : constant Float := 3.0;

end DPSS_Constants;

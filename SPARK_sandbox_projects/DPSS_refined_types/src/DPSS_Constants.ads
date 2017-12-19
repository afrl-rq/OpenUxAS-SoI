-- -------------------------------------------------------------------------- --
-- DPSS_Constants.ads           Dependable Computing

with DPSS_Data_Types;

package DPSS_Constants with SPARK_Mode is

  -- const P_GLOBAL : Base_Types::Float = 10.0;
  --
  -- This should really be a position type, so I've done that here.
  P_GLOBAL : constant DPSS_Data_Types.position_type := 10.0;

  -- const LEFT : int = -1;
  LEFT : constant Integer := -1;

  -- const RIGHT : int = 1;
  RIGHT : constant Integer := 1;

  -- const N_int : int = 3; --Number of vehicles
  N_int : constant Integer := 3;

end DPSS_Constants;

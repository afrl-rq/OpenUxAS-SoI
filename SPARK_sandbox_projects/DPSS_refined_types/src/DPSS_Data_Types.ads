-- -------------------------------------------------------------------------- --
-- DPSS_Data_types.ads          Dependable Computing

package DPSS_Data_Types with SPARK_Mode is
  -- AADL Direction Type:
  --
  --   data Direction_Type extends Base_Types::Integer
  --   end Direction_Type;
  --
  -- Since the direction type can be only -1 or 1, I'm restricting the range and
  -- using a type invariant to ensure that only legal values are assigned.
  subtype direction_type is Integer range -1 .. 1 with
    Predicate => (direction_type = -1 or direction_type = 1);

  -- AADL Position_type:
  --
  --    data Position_Type extends Base_Types::Float
  --    end Position_Type;
  --
  -- Since the original is unconstrained, I leave it unconstrained here. Use of
  -- subtype is justified because the AADL requires no explicit conversions for
  -- application of this type.
  subtype position_type is Float range Float'First .. Float'Last;
end DPSS_Data_Types;

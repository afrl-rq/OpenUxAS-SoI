-- -------------------------------------------------------------------------- --
-- DPSS_Data_types.ads          Dependable Computing

package DPSS_Data_Types with SPARK_Mode is
  -- AADL Direction Type:
  --
  --   data Direction_Type extends Base_Types::Integer
  --   end Direction_Type;
  --
  -- Since the original is unconstrained, I leave it unconstrained here. Use of
  -- subtype is justified because the AADL requires no explicit conversions for
  -- application of this type.
  subtype direction_type is Integer range Integer'First .. Integer'Last;

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

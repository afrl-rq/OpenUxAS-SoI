--  linear/geographical conversions

generic
   type Real is digits <>;
package Unit_Conversion_Utilities is

   type Unit_Converter is tagged private;

   procedure Initialize
     (This              : out Unit_Converter;
      LatitudeInit_Rad  : Real;
      LongitudeInit_rad : Real);

   --  FROM LAT/LONG TO NORTH/EAST

   procedure Convert_LatLong_Degrees_To_NorthEast_Meters
     (This          : in out Unit_Converter;
      Latitude_Deg  : Real;
      Longitude_Deg : Real;
      North         : out Real;
      East          : out Real);

   --  FROM NORTH/EAST TO LAT/LONG
   --  ...

   --  const double m_dRadiusEquatorial_m{6378135.0};
   dRadiusEquatorial_m : constant := 6_378_135.0;
   --  const double m_dFlattening{3.352810664724998e-003};
   dFlattening : constant := 3.352810664724998e-003;
   --  const double m_dEccentricitySquared{6.694379990096503e-003};
   dEccentricitySquared : constant := 6.694379990096503e-003;

private

   type Unit_Converter is tagged record
      --  static double m_dLatitudeInitial_rad;
      m_dLatitudeInitial_rad : Real;
      --  static double m_dLongitudeInitial_rad;
      m_dLongitudeInitial_rad : Real;
      --  static double m_dRadiusMeridional_m;
      m_dRadiusMeridional_m : Real;
      --  static double m_dRadiusTransverse_m;
      m_dRadiusTransverse_m : Real;
      --  static double m_dRadiusSmallCircleLatitude_m;
      m_dRadiusSmallCircleLatitude_m : Real;
      --  Static Bool M_BInitialized;
      Initialized : Boolean := False;
   end record;

end Unit_Conversion_Utilities;

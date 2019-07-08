package body afrl.cmasi.OperatingRegion.SPARK_Boundary with SPARK_Mode => Off is

   ---------------
   -- Get_Areas --
   ---------------

   function Get_Areas
     (Region : OperatingRegion) return OperatingRegionAreas
   is
      InAreas  : constant afrl.cmasi.OperatingRegion.Vect_Int64_Acc := Region.getKeepInAreas;
      OutAreas : constant afrl.cmasi.OperatingRegion.Vect_Int64_Acc := Region.getKeepInAreas;
   begin
      return R : OperatingRegionAreas do
         for E of InAreas.all loop
            Int64_Vects.Append (R.KeepInAreas, E);
         end loop;
         for E of OutAreas.all loop
            Int64_Vects.Append (R.KeepOutAreas, E);
         end loop;
      end return;
   end Get_Areas;

end afrl.cmasi.OperatingRegion.SPARK_Boundary;

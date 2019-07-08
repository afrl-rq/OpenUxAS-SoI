with Common_Formal_Containers; use Common_Formal_Containers;

package AFRL.CMASI.OperatingRegion.SPARK_Boundary with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   type OperatingRegionAreas is record
      KeepInAreas  : Int64_Vect;
      KeepOutAreas : Int64_Vect;
   end record;

   function Get_Areas
     (Region : OperatingRegion) return OperatingRegionAreas
     with Global => null;
end AFRL.CMASI.OperatingRegion.SPARK_Boundary;

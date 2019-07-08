package afrl.impact.ImpactPointSearchTask.SPARK_Boundary with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   --  This wrapper is only introduced for termination

   function Get_SearchLocationID (X : ImpactPointSearchTask) return Int64;
end afrl.impact.ImpactPointSearchTask.SPARK_Boundary;

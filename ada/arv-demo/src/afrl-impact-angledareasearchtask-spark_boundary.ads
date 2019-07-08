package afrl.impact.AngledAreaSearchTask.SPARK_Boundary with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   --  This wrapper is only introduced for termination

   function Get_SearchAreaID (X : AngledAreaSearchTask) return Int64;
end afrl.impact.AngledAreaSearchTask.SPARK_Boundary;

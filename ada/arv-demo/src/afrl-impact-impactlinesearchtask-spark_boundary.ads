package afrl.impact.ImpactLineSearchTask.SPARK_Boundary with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   --  This wrapper is only introduced for termination

   function Get_LineID (X : ImpactLineSearchTask) return Int64;
end afrl.impact.ImpactLineSearchTask.SPARK_Boundary;

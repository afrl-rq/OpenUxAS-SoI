package body afrl.impact.AngledAreaSearchTask.SPARK_Boundary with SPARK_Mode => Off is

   function Get_SearchAreaID (X : AngledAreaSearchTask) return Int64 renames
     getSearchAreaID;
end afrl.impact.AngledAreaSearchTask.SPARK_Boundary;

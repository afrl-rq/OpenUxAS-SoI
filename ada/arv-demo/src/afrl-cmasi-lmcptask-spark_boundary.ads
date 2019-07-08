with afrl.impact.AngledAreaSearchTask;
with afrl.impact.ImpactLineSearchTask;
with afrl.impact.ImpactPointSearchTask;

package afrl.cmasi.lmcpTask.SPARK_Boundary with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);
   --  This package introduces a private type hiding an access to a
   --  LmcpTask.

   type Task_Kind is (AngledAreaSearchTask, ImpactLineSearchTask, ImpactPointSearchTask, Other_Task);

   type Task_Kind_And_Id (Kind : Task_Kind := Other_Task) is record
      case Kind is
      when AngledAreaSearchTask =>
         SearchAreaID : Int64;
      when ImpactLineSearchTask =>
         LineID : Int64;
      when ImpactPointSearchTask =>
         SearchLocationID : Int64;
      when Other_Task =>
         null;
      end case;
   end record;

   function Get_Kind_And_Id (X : LmcpTask_Any) return Task_Kind_And_Id with
     Global => null,
     SPARK_Mode => Off;

private
   pragma SPARK_Mode (Off);

   function Get_Kind_And_Id (X : LmcpTask_Any) return Task_Kind_And_Id is
     (if X.getLmcpTypeName = afrl.impact.AngledAreaSearchTask.Subscription then
        (Kind         => AngledAreaSearchTask,
         SearchAreaID => afrl.impact.AngledAreaSearchTask.AngledAreaSearchTask (X.all).GetSearchAreaID)
      elsif X.getLmcpTypeName = afrl.impact.ImpactLineSearchTask.Subscription then
        (Kind   => ImpactLineSearchTask,
         LineID => afrl.impact.ImpactLineSearchTask.ImpactLineSearchTask (X.all).getLineID)
      elsif X.getLmcpTypeName = afrl.impact.ImpactPointSearchTask.Subscription then
        (Kind             => ImpactPointSearchTask,
         SearchLocationId => afrl.impact.ImpactPointSearchTask.ImpactPointSearchTask (X.all).getSearchLocationID)
      else (Kind => Other_task));

end afrl.cmasi.lmcpTask.SPARK_Boundary;

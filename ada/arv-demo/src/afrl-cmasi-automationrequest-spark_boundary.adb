
package body afrl.cmasi.AutomationRequest.SPARK_Boundary with SPARK_Mode => Off is

   --------------------
   -- Get_EntityList --
   --------------------

   function Get_EntityList
     (Request : AutomationRequest) return Int64_Vect
   is
      L : constant Vect_Int64_Acc := Request.getEntityList;
   begin
      return R : Int64_Vect do
         for E of L.all loop
            Int64_Vects.Append (R, E);
         end loop;
      end return;
   end Get_EntityList;

   -------------------------
   -- Get_OperatingRegion --
   -------------------------

   function Get_OperatingRegion
     (Request : AutomationRequest) return Int64
         renames getOperatingRegion;

   ------------------
   -- Get_TaskList --
   ------------------

   function Get_TaskList
     (Request : AutomationRequest) return Int64_Vect
   is
      L : constant Vect_Int64_Acc := Request.getTaskList;
   begin
      return R : Int64_Vect do
         for E of L.all loop
            Int64_Vects.Append (R, E);
         end loop;
      end return;
   end Get_TaskList;
end afrl.cmasi.AutomationRequest.SPARK_Boundary;

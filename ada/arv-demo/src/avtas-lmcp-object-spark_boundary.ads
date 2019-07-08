package avtas.lmcp.object.SPARK_Boundary with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   type My_Object_Any is private;
   function Deref (X : My_Object_Any) return Object'Class with
     Global => null,
     Inline;
   function Wrap (X : Object_Any) return My_Object_Any with
     Global => null,
     Inline,
     SPARK_Mode => Off;
   function Unwrap (X : My_Object_Any) return Object_Any with
     Global => null,
     Inline,
     SPARK_Mode => Off;
private
   pragma SPARK_Mode (Off);
   type My_Object_Any is new Object_Any;
   function Deref (X : My_Object_Any) return Object'Class is
     (X.all);
   function Wrap (X : Object_Any) return My_Object_Any is
     (My_Object_Any (X));
   function Unwrap (X : My_Object_Any) return Object_Any is
     (Object_Any (X));
end avtas.lmcp.object.SPARK_Boundary;

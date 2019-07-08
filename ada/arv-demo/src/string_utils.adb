package body String_Utils is

   ---------------
   -- To_String --
   ---------------

   function To_String (Input : Int32) return String is
      Result : constant String := Input'Image;
   begin
      if Input < 0 then
         return Result;  -- including the first char, which is the minus sign
      else
         return Result (2 .. Result'Last);
      end if;
   end To_String;

   ---------------
   -- To_String --
   ---------------

   function To_String (Input : Int64) return String is
      Result : constant String := Input'Image;
   begin
      if Input < 0 then
         return Result;  -- including the first char, which is the minus sign
      else
         return Result (2 .. Result'Last);
      end if;
   end To_String;

   ---------------
   -- To_String --
   ---------------

   function To_String (Input : UInt32) return String is
      Result : constant String := Input'Image;
   begin
      return Result (2 .. Result'Last);
   end To_String;

end String_Utils;

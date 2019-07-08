with Ada.Text_IO;            use Ada.Text_IO;
with AVTAS.LMCP.Types;       use AVTAS.LMCP.Types;
with AVTAS.LMCP.ByteBuffers; use AVTAS.LMCP.ByteBuffers;
with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;

procedure Test_ByteBuffers is
   Byte_Input    : constant Byte := 42;
   String_Input  : constant String := "Hello World!";
   UInt32_Input  : constant UInt32 := 42;
   Real32_Input  : constant Real32 := 42.42;
   Boolean_Input : constant Boolean := True;
   UInt64_Input  : constant UInt64 := 84;

   Buffer : ByteBuffer (Capacity => 1024);
begin
   --  NB: the order of the following must match the order of the calls to Get_*
   Put_Line ("Putting Byte");
   Buffer.Put_Byte (Byte_Input);
   Put_Line ("Putting String");
   Buffer.Put_String (String_Input);
   Put_Line ("Putting UInt32");
   Buffer.Put_UInt32 (UInt32_Input);
   Put_Line ("Putting Unbounded_String");
   Buffer.Put_Unbounded_String (To_Unbounded_String (String_Input));
   Put_Line ("Putting Real32");
   Buffer.Put_Real32 (Real32_Input);
   Put_Line ("Putting Boolean");
   Buffer.Put_Boolean (Boolean_Input);
   Put_Line ("Putting UInt64");
   Buffer.Put_UInt64 (UInt64_Input);

   New_Line;

   --  now we read back what was written

   Buffer.Rewind;

   --  NB: the order of the following must match the order of the calls to Put_*

   Put_Line ("Getting Byte");
   declare
      Output : Byte;
   begin
      Buffer.Get_Byte (Output);
      pragma Assert (Output = Byte_Input);
   end;

   Put_Line ("Getting String");
   declare
      Output : String (String_Input'Range);
      Last   : Natural;
   begin
      Buffer.Get_String (Output, Last);
      pragma Assert (Last = String_Input'Length);
      pragma Assert (Output (1 .. Last) = String_Input);
   end;

   Put_Line ("Getting UInt32");
   declare
      Output : UInt32;
   begin
      Buffer.Get_UInt32 (Output);
      pragma Assert (Output = UInt32_Input);
   end;

   Put_Line ("Getting Unbounded_String");
   declare
      Output : Unbounded_String;
   begin
      Buffer.Get_Unbounded_String (Output);
      pragma Assert (To_String (Output) = String_Input);
   end;

   Put_Line ("Getting Real32");
   declare
      Output : Real32;
   begin
      Buffer.Get_Real32 (Output);
      pragma Assert (Output = Real32_Input);
   end;

   Put_Line ("Getting Boolean");
   declare
      Output : Boolean;
   begin
      Buffer.Get_Boolean (Output);
      pragma Assert (Output = Boolean_Input);
   end;

   Put_Line ("Getting UInt64");
   declare
      Output : UInt64;
   begin
      Buffer.Get_UInt64 (Output);
      pragma Assert (Output = UInt64_Input);
   end;

   New_Line;
   Put_Line ("Testing completed");
end Test_ByteBuffers;

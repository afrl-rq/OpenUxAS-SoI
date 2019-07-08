package body UxAS.Common.Sentinel_Serial_Buffers is

   -----------------------------
   -- Get_Next_Payload_String --
   -----------------------------

   procedure Get_Next_Payload_String
     (This           : in out Sentinel_Serial_Buffer;
      New_Data_Chunk : String;
      Result         : out String)
   is
   begin
      --  Generated stub: replace with real body!
      pragma Compile_Time_Warning (Standard.True, "Get_Next_Payload_String unimplemented");
      raise Program_Error with "Unimplemented procedure Get_Next_Payload_String";
   end Get_Next_Payload_String;

   --------------------------------
   -- Create_Sentinelized_String --
   --------------------------------

   function Create_Sentinelized_String (Data : String) return String is
   begin
      --  Generated stub: replace with real body!
      pragma Compile_Time_Warning (Standard.True, "Create_Sentinelized_String unimplemented");
      return raise Program_Error with "Unimplemented function Create_Sentinelized_String";
   end Create_Sentinelized_String;

   -------------------------
   -- Calculated_Checksum --
   -------------------------

   function Calculated_Checksum (Str : String) return UInt32 is
      Result : UInt32 := 0;
   begin
      for C of Str loop
         Result := Result + Character'Pos (C);
      end loop;
      return Result;
   end Calculated_Checksum;

   ----------------------------------------------
   -- Get_Detect_Sentinel_Base_Strings_Message --
   ----------------------------------------------

   function Get_Detect_Sentinel_Base_Strings_Message (Data : String) return String is
   begin
      --  Generated stub: replace with real body!
      pragma Compile_Time_Warning (Standard.True, "Get_Detect_Sentinel_Base_Strings_Message unimplemented");
      return raise Program_Error with "Unimplemented function Get_Detect_Sentinel_Base_Strings_Message";
   end Get_Detect_Sentinel_Base_Strings_Message;

end UxAS.Common.Sentinel_Serial_Buffers;

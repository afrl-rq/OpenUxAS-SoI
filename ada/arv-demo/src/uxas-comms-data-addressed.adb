with GNAT.String_Split;
with Ada.Strings.Fixed;

package body UxAS.Comms.Data.Addressed is

   ----------------------
   -- Is_Valid_Address --
   ----------------------

   function Is_Valid_Address (Address : String) return Boolean is
      Delimiter_Pos : Natural;
      use Ada.Strings.Fixed;
   begin
      if Address'Length = 0 then
         return False;
      end if;
      Delimiter_Pos := Index (Source  => Address, Pattern => Address_Attributes_Delimiter);
      if Delimiter_Pos /= 0 then -- found a delimiter
         return False;
      end if;
      return True;
   end Is_Valid_Address;

   -----------------------------
   -- Set_Address_And_Payload --
   -----------------------------

   procedure Set_Address_And_Payload
     (This    : in out Addressed_Message;
      Address : String;
      Payload : String;
      Result  : out Boolean)
   is
   begin
      if not Is_Valid_Address (Address) or Payload'Length = 0 then
         This.Is_Valid := False;
         Result := False;
         return;
      end if;

      Copy (Address, To => This.Address);
      Copy (Payload, To => This.Payload);
      Copy (Address & Address_Attributes_Delimiter & Payload, To => This.Content_String);

      This.Is_Valid := True;
      Result := True;
   end Set_Address_And_Payload;

   ---------------------------------------------------
   -- Set_Address_And_Payload_From_Delimited_String --
   ---------------------------------------------------

   procedure Set_Address_And_Payload_From_Delimited_String
     (This             : in out Addressed_Message;
      Delimited_String : String;
      Result           : out Boolean)
   is
   begin
      if Delimited_String'Length >= Minimum_Delimited_Address_Message_String_Length then
         Parse_Addressed_Message_String_And_Set_Fields (This, Delimited_String, Result);
      else
         This.Is_Valid := False;
         Result := False;
      end if;
   end Set_Address_And_Payload_From_Delimited_String;

   --------------
   -- Is_Valid --
   --------------

   function Is_Valid (This : Addressed_Message) return Boolean is
     (This.Is_Valid);

   -------------
   -- Address --
   -------------

   function Address (This : Addressed_Message) return String is
     (Value (This.Address));

   -------------
   -- Payload --
   -------------

   function Payload (This : Addressed_Message) return String is
     (Value (This.Payload));

   --------------------
   -- Content_String --
   --------------------

   function Content_String (This : Addressed_Message) return String is
     (Value (This.Content_String));

   ---------------------------------------------------
   -- Parse_Addressed_Message_String_And_Set_Fields --
   ---------------------------------------------------

   procedure Parse_Addressed_Message_String_And_Set_Fields
     (This             : in out Addressed_Message;
      Delimited_String : String;
      Result           : out Boolean)
   is
      use GNAT.String_Split;
      Parts : Slice_Set;
   begin
      Create (Parts,
              From       => Delimited_String,
              Separators => Address_Attributes_Delimiter,
              Mode       => Single); -- contiguous delimiters are NOT treated as a single delimiter;

      This.Is_Valid := False;
      Result := False;
      if Slice_Count (Parts) /= 2 then
         return;
      elsif Slice (Parts, 1) = "" or Slice (Parts, 2) = "" then
         return;
      else
         Set_Address_And_Payload
           (This,
            Address => Slice (Parts, 1),
            Payload => Slice (Parts, 2),
            Result  => Result);
      end if;
   end Parse_Addressed_Message_String_And_Set_Fields;

end UxAS.Comms.Data.Addressed;

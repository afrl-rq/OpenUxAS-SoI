with GNAT.String_Split;
with UxAS.Comms.Data.Addressed;  use UxAS.Comms.Data.Addressed;

package body UxAS.Comms.Data is

   --------------------
   -- Set_Attributes --
   --------------------

   procedure Set_Attributes
     (This              : in out Message_Attributes;
      Content_Type      : String;
      Descriptor        : String;
      Source_Group      : String;
      Source_Entity_Id  : String;
      Source_Service_Id : String;
      Result            : out Boolean)
   is
   begin
      Result := False;
      This.Is_Valid := False;

      if Content_Type'Length = 0 then
         return;
      end if;

      if Descriptor'Length = 0 then
         return;
      end if;

      if Source_Entity_Id'Length = 0 then
         return;
      end if;

      if Source_Service_Id'Length = 0 then
         return;
      end if;

      Copy (Content_Type,      To => This.Content_Type);
      Copy (Descriptor,        To => This.Descriptor);
      Copy (Source_Group,      To => This.Source_Group);
      Copy (Source_Entity_Id,  To => This.Source_Entity_Id);
      Copy (Source_Service_Id, To => This.Source_Service_Id);

      Copy (This.Content_Type      & Addressed.Field_Delimiter &
            This.Descriptor        & Addressed.Field_Delimiter &
            This.Source_Group      & Addressed.Field_Delimiter &
            This.Source_Entity_Id  & Addressed.Field_Delimiter &
            This.Source_Service_Id,
            To => This.Content_String);

      This.Is_Valid := True;     -- already determined by preconditions...
      Result := True;
   end Set_Attributes;

   ------------------------------
   -- Update_Source_Attributes --
   ------------------------------

   procedure Update_Source_Attributes
     (This              : in out Message_Attributes;
      Source_Group      : String;
      Source_Entity_Id  : String;
      Source_Service_Id : String;
      Result            : out Boolean)
   is
   begin
      Copy (Source_Group,      To => This.Source_Group);
      Copy (Source_Entity_Id,  To => This.Source_Entity_Id);
      Copy (Source_Service_Id, To => This.Source_Service_Id);

      Copy (This.Content_Type      & Addressed.Field_Delimiter &
            This.Descriptor        & Addressed.Field_Delimiter &
            This.Source_Group      & Addressed.Field_Delimiter &
            This.Source_Entity_Id  & Addressed.Field_Delimiter &
            This.Source_Service_Id & Addressed.Field_Delimiter,
            To => This.Content_String);

      This.Is_Valid := True;     -- already determined by preconditions...
      Result := True;
   end Update_Source_Attributes;

   ------------------------------------------
   -- Set_Attributes_From_Delimited_String --
   ------------------------------------------

   procedure Set_Attributes_From_Delimited_String
     (This              : in out Message_Attributes;
      Delimited_String  : String;
      Result            : out Boolean)
   is
   begin
      Parse_Message_Attributes_String_And_Set_Fields (This, Delimited_String, Result);
   end Set_Attributes_From_Delimited_String;

   --------------
   -- Is_Valid --
   --------------

   function Is_Valid (This : Message_Attributes) return Boolean is
     (This.Is_Valid);

   --------------------------
   -- Payload_Content_Type --
   --------------------------

   function Payload_Content_Type (This : Message_Attributes) return String is
     (Value (This.Content_Type));

   ------------------------
   -- Payload_Descriptor --
   ------------------------

   function Payload_Descriptor (This : Message_Attributes) return String is
     (Value (This.Descriptor));

   ------------------
   -- Source_Group --
   ------------------

   function Source_Group (This : Message_Attributes) return String is
     (Value (This.Source_Group));

   ----------------------
   -- Source_Entity_Id --
   ----------------------

   function Source_Entity_Id (This : Message_Attributes) return String is
     (Value (This.Source_Entity_Id));

   -----------------------
   -- Source_Service_Id --
   -----------------------

   function Source_Service_Id (This : Message_Attributes) return String is
     (Value (This.Source_Service_Id));

   --------------------
   -- Content_String --
   --------------------

   function Content_String (This : Message_Attributes) return String is
     (Value (This.Content_String));

   ----------------------------------------------------
   -- Parse_Message_Attributes_String_And_Set_Fields --
   ----------------------------------------------------

   procedure Parse_Message_Attributes_String_And_Set_Fields
     (This             : in out Message_Attributes;
      Delimited_String : String;
      Result           : out Boolean)
   is
      use GNAT.String_Split;
      Tokens : Slice_Set;
   begin
      Create (Tokens,
              From       => Delimited_String,
              Separators => Field_Delimiter,
              Mode       => Single); -- contiguous delimiters are NOT treated as a single delimiter

      if Slice_Count (Tokens) = Attribute_Count then
         This.Set_Attributes
           (Content_Type      => Slice (Tokens, 1),
            Descriptor        => Slice (Tokens, 2),
            Source_Group      => Slice (Tokens, 3),
            Source_Entity_Id  => Slice (Tokens, 4),
            Source_Service_Id => Slice (Tokens, 5),
            Result            => Result);
      else
         Result := False;
         This.Is_Valid := False;
      end if;
   end Parse_Message_Attributes_String_And_Set_Fields;

end UxAS.Comms.Data;

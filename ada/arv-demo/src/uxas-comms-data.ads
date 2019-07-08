--  see OpenUxAS\src\Communications\MessageAttributes.h

package UxAS.Comms.Data is

   type Message_Attributes is tagged private;

   type Message_Attributes_Ref  is access all Message_Attributes;
   type Message_Attributes_View is access constant Message_Attributes;
   type Any_Message_Attributes  is access Message_Attributes'Class;

   Minimum_Delimited_Address_Attribute_Message_String_Length : constant := 8;

   Attribute_Count : constant := 5;

   --      static const std::string&
   --      s_typeName() { static std::string s_string("MessageAttributes"); return (s_string); };
   Type_Name : constant String := "MessageAttributes";

   --  bool
   --  setAttributes(const std::string contentType,
   --                const std::string descriptor,
   --                const std::string sourceGroup,
   --                const std::string sourceEntityId,
   --                const std::string sourceServiceId)
   procedure Set_Attributes
     (This              : in out Message_Attributes;
      Content_Type      : String;
      Descriptor        : String;
      Source_Group      : String;     --  can be an empty string
      Source_Entity_Id  : String;
      Source_Service_Id : String;
      Result            : out Boolean);
--     with Pre'Class =>
--         Content_Type'Length      in 1 .. Content_Type_Max_Length      and then
--         Descriptor'Length        in 1 .. Descriptor_Max_Length        and then
--         Source_Group'Length      <=      Source_Group_Max_Length      and then
--         Source_Entity_Id'Length  in 1 .. Source_Entity_Id_Max_Length  and then
--         Source_Service_Id'Length in 1 .. Source_Service_Id_Max_Length;

   --  bool
   --  updateSourceAttributes(const std::string sourceGroup, const std::string sourceEntityId, const std::string sourceServiceId)
   procedure Update_Source_Attributes
     (This              : in out Message_Attributes;
      Source_Group      : String;
      Source_Entity_Id  : String;      -- can be empty
      Source_Service_Id : String;
      Result            : out Boolean)
   with Pre'Class =>
       Source_Group'Length      <=      Source_Group_Max_Length      and then
       Source_Entity_Id'Length  in 1 .. Source_Entity_Id_Max_Length  and then
       Source_Service_Id'Length in 1 .. Source_Service_Id_Max_Length;

   --      bool
   --      setAttributesFromDelimitedString(const std::string delimitedString)
   procedure Set_Attributes_From_Delimited_String
     (This              : in out Message_Attributes;
      Delimited_String  : String;
      Result            : out Boolean)
   with Pre'Class =>
       Delimited_String'Length >= Minimum_Delimited_Address_Attribute_Message_String_Length;

   --  bool
   --  isValid()
   function Is_Valid (This : Message_Attributes) return Boolean;

   --  Content type of payload (e.g., "json", "lmcp", "text", "xml").
   --  Valid values for content type are a controlled list. Cannot be an empty
   --  string.
   --      const std::string&
   --      getContentType() const
   function Payload_Content_Type (This : Message_Attributes) return String with
     Post'Class => Payload_Content_Type'Result'Length > 0;

   --  Descriptive qualifier for the payload.
   --  Example values: "afrl.cmasi.AirVehicleState" (LMCP full type name)
   --  for case LMCP payload; json qualifying descriptor. Generally, is additional
   --  description of the payload beyond the content type value. Valid values
   --  for descriptor are a controlled list - but less constrained than content
   --  type. TODO REVIEW Cannot be an empty string.
   --
   --  const std::string&
   --  getDescriptor() const
   function Payload_Descriptor (This : Message_Attributes) return String;

   --  Multi-cast address to which the sending service subscribes. Can be an empty string.
   --  const std::string&
   --  getSourceGroup() const
   function Source_Group (This : Message_Attributes) return String;

   --  Entity ID of the host of the sending service.
   --  Cannot be an empty string.
   --  const std::string&
   --  getSourceEntityId() const
   function Source_Entity_Id (This : Message_Attributes) return String with
     Post'Class => Source_Entity_Id'Result'Length > 0;

   --  Service ID of the sending service. Cannot be an empty string.
   --  const std::string&
   --  getSourceServiceId() const
   function Source_Service_Id (This : Message_Attributes) return String with
     Post'Class => Source_Service_Id'Result'Length > 0;

   --  Attribute fields combined into a single, delimited string.
   --  Returns concatenated attribute fields.
   --  const std::string&
   --  getString() const
   function Content_String (This : Message_Attributes) return String;

private

   --  bool
   --  parseMessageAttributesStringAndSetFields(const std::string delimitedString)
   procedure Parse_Message_Attributes_String_And_Set_Fields
     (This             : in out Message_Attributes;
      Delimited_String : String;
      Result           : out Boolean);

   type Message_Attributes is tagged record
      Is_Valid          : Boolean := False;
      Content_String    : Dynamic_String (Capacity => Content_String_Max_Length);      --  note different name (not m_string)
      Content_Type      : Dynamic_String (Capacity => Content_Type_Max_Length);
      Descriptor        : Dynamic_String (Capacity => Content_Type_Max_Length);
      Source_Group      : Dynamic_String (Capacity => Source_Group_Max_Length);
      Source_Entity_Id  : Dynamic_String (Capacity => Source_Entity_Id_Max_Length);
      Source_Service_Id : Dynamic_String (Capacity => Source_Service_Id_Max_Length);
   end record;

end UxAS.Comms.Data;

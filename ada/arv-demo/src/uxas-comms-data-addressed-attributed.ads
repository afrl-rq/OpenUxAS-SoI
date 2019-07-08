--  see OpenUxAS\src\Communications\AddressedAttributedMessage.h

package UxAS.Comms.Data.Addressed.Attributed is

   Type_Name : constant String := "AddressedAttributedMessage";

   Minimum_Delimited_Address_Attribute_Message_String_Length : constant := 11;

   Address_Attributes_Delimiter : constant String := Addressed.Address_Attributes_Delimiter; -- re-export

   Field_Delimiter : constant String := UxAS.Comms.Data.Addressed.Field_Delimiter; -- re-export

   type Addressed_Attributed_Message is new Addressed_Message with private;

   type Addressed_Attributed_Message_Ref  is access all Addressed_Attributed_Message;

   type Any_Addressed_Attributed_Message  is access all Addressed_Attributed_Message'Class;

   --  bool
   --  setAddressAttributesAndPayload
   --     (const std::string address,
   --      const std::string contentType,
   --      const std::string descriptor,
   --      const std::string sourceGroup,
   --      const std::string sourceEntityId,
   --      const std::string sourceServiceId,
   --      const std::string payload)
   procedure Set_Address_Attributes_And_Payload
     (This              : in out Addressed_Attributed_Message;
      Address           : String;
      Content_Type      : String;
      Descriptor        : String;
      Source_Group      : String;  -- TODO: can be empty???
      Source_Entity_Id  : String;
      Source_Service_Id : String;
      Payload           : String;
      Result            : out Boolean)
   with Pre'Class =>
       Address'Length           in 1 .. Address_Max_Length           and then
       Is_Valid_Address (Address)                                    and then
       Content_Type'Length      in 1 .. Content_Type_Max_Length      and then
       Descriptor'Length        in 1 .. Descriptor_Max_Length        and then
       Source_Group'Length      <=      Source_Group_Max_Length      and then
       Source_Entity_Id'Length  in 1 .. Source_Entity_Id_Max_Length  and then
       Source_Service_Id'Length in 1 .. Source_Service_Id_Max_Length;

   --  bool
   --  updateSourceAttributes(const std::string sourceGroup, const std::string sourceEntityId, const std::string sourceServiceId)
   procedure Update_Source_Attributes
     (This              : in out Addressed_Attributed_Message;
      Source_Group      : String;
      Source_Entity_Id  : String;
      Source_Service_Id : String;
      Result            : out Boolean)
   with Pre'Class =>
       Source_Group'Length      <=      Source_Group_Max_Length      and then
       Source_Entity_Id'Length  in 1 .. Source_Entity_Id_Max_Length  and then
       Source_Service_Id'Length in 1 .. Source_Service_Id_Max_Length;

   procedure Update_Address
     (This    : in out Addressed_Attributed_Message;
      Address : String;
      Result  : out Boolean)
   with Pre'Class =>
       Address'Length in 1 .. Address_Max_Length;

   procedure Set_Address_Attributes_And_Payload_From_Delimited_String
     (This             : in out Addressed_Attributed_Message;
      Delimited_String : String;
      Result           : out Boolean)
   with Pre'Class =>
       Delimited_String'Length >= Minimum_Delimited_Address_Attribute_Message_String_Length;

   --  Message address, attributes and payload combined into a single, delimited string.
   --  virtual
   --  const std::string&
   --  getString() const
   overriding
   function Content_String (This : Addressed_Attributed_Message) return String;

   --  Ownership transfer accessor for message attributes.
   --  std::unique_ptr<MessageAttributes>
   --  getMessageAttributesOwnership()
   function Message_Attributes_Ownership (This : Addressed_Attributed_Message) return Message_Attributes_Ref;
   --  Note: In Ada, this routine makes no change, it just return the current pointer

   --  Read-only accessor for message attributes.
   --  const std::unique_ptr<MessageAttributes>&
   --  getMessageAttributesReference()
   function Message_Attributes_Reference (This : Addressed_Attributed_Message) return Message_Attributes_View;

private

   type Addressed_Attributed_Message is new Addressed_Message with record
      --  std::unique_ptr<MessageAttributes> m_messageAttributes;
      Attributes : Message_Attributes_Ref; -- TODO: indirection for sake of ownership and read-only view?
   end record;

   --  bool
   --  parseAddressedAttributedMessageStringAndSetFields(const std::string delimitedString)
   procedure Parse_Addressed_Attributed_Message_String_And_Set_Fields
     (This             : in out Addressed_Attributed_Message;
      Delimited_String : String;
      Result           : out Boolean)
  with Pre'Class => Delimited_String'Length >= Minimum_Delimited_Address_Attribute_Message_String_Length;


end UxAS.Comms.Data.Addressed.Attributed;

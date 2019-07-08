with Ada.Strings.Fixed;

package body UxAS.Comms.Data.Addressed.Attributed is

   ----------------------------------------
   -- Set_Address_Attributes_And_Payload --
   ----------------------------------------

   procedure Set_Address_Attributes_And_Payload
     (This              : in out Addressed_Attributed_Message;
      Address           : String;
      Content_Type      : String;
      Descriptor        : String;
      Source_Group      : String;
      Source_Entity_Id  : String;
      Source_Service_Id : String;
      Payload           : String;
      Result            : out Boolean)
   is
   begin
      if not UxAS.Comms.Data.Addressed.Is_Valid_Address (Address) then
         This.Is_Valid := False;
         Result := False;
         return;
      end if;

      if Payload'Length = 0 then
         This.Is_Valid := False;
         Result := False;
         return;
      end if;

      This.Attributes := new Message_Attributes;

      This.Attributes.Set_Attributes
        (Content_Type      => Content_Type,
         Descriptor        => Descriptor,
         Source_Group      => Source_Group,
         Source_Entity_Id  => Source_Entity_Id,
         Source_Service_Id => Source_Service_Id,
         Result            => Result);
      if Result then
         Copy (Address, To => This.Address);
         Copy (Payload, To => This.Payload);
         Copy (This.Address & Address_Attributes_Delimiter &
               This.Attributes.Content_String & Address_Attributes_Delimiter &
               This.Payload,
               To => This.Content_String);
         This.Is_Valid := True;
      else
         This.Is_Valid := False;
      end if;
   end Set_Address_Attributes_And_Payload;

   ------------------------------
   -- Update_Source_Attributes --
   ------------------------------

   procedure Update_Source_Attributes
     (This              : in out Addressed_Attributed_Message;
      Source_Group      : String;
      Source_Entity_Id  : String;
      Source_Service_Id : String;
      Result            : out Boolean)
   is
   begin
      --  m_isValid = m_isValid & m_messageAttributes->updateSourceAttributes(sourceGroup, sourceEntityId, sourceServiceId);
      This.Attributes.Update_Source_Attributes
        (Source_Group      => Source_Group,
         Source_Entity_Id  => Source_Entity_Id,
         Source_Service_Id => Source_Service_Id,
         Result            => Result);
      This.Is_Valid := This.Is_Valid and Result;

      --  m_string = m_address + s_addressAttributesDelimiter() + m_messageAttributes->getString() + s_addressAttributesDelimiter() + m_payload;
      Copy (This.Address                   & Address_Attributes_Delimiter &
            This.Attributes.Content_String & Address_Attributes_Delimiter &
            This.Payload,
            To => This.Content_String);

      Result := This.Is_Valid;
   end Update_Source_Attributes;

   --------------------
   -- Update_Address --
   --------------------

   procedure Update_Address
     (This    : in out Addressed_Attributed_Message;
      Address : String;
      Result  : out Boolean)
   is
   begin
      Copy (Address, To => This.Address);
      Copy (This.Address                   & Address_Attributes_Delimiter &
            This.Attributes.Content_String & Address_Attributes_Delimiter &
            This.Payload,
            To => This.Content_String);
      Result := This.Is_Valid;
   end Update_Address;

   --------------------------------------------------------------
   -- Set_Address_Attributes_And_Payload_From_Delimited_String --
   --------------------------------------------------------------

   procedure Set_Address_Attributes_And_Payload_From_Delimited_String
     (This             : in out Addressed_Attributed_Message;
      Delimited_String : String;
      Result           : out Boolean)
   is
   begin
      -- we check this via precondition:
      --    if (delimitedString.length() >= s_minimumDelimitedAddressAttributeMessageStringLength)

      --  return (parseAddressedAttributedMessageStringAndSetFields(std::move(delimitedString)));
      Parse_Addressed_Attributed_Message_String_And_Set_Fields (This, Delimited_String, Result);
   end Set_Address_Attributes_And_Payload_From_Delimited_String;

   --------------------
   -- Content_String --
   --------------------

   overriding
   function Content_String
     (This : Addressed_Attributed_Message)
      return String
   is
   begin
      if This.Attributes /= null then
         return Value (This.Content_String);
      else
         return "";
      end if;
   end Content_String;

   ----------------------------------
   -- Message_Attributes_Ownership --
   ----------------------------------

   function Message_Attributes_Ownership
     (This : Addressed_Attributed_Message)
      return Message_Attributes_Ref
   is
      (This.Attributes);

   ----------------------------------
   -- Message_Attributes_Reference --
   ----------------------------------

   function Message_Attributes_Reference
     (This : Addressed_Attributed_Message)
      return Message_Attributes_View
   is
      (Message_Attributes_View (This.Attributes));

   --------------------------------------------------------------
   -- Parse_Addressed_Attributed_Message_String_And_Set_Fields --
   --------------------------------------------------------------

   procedure Parse_Addressed_Attributed_Message_String_And_Set_Fields
     (This             : in out Addressed_Attributed_Message;
      Delimited_String : String;
      Result           : out Boolean)
   is
      use Ada.Strings.Fixed;

      EndOfAddressDelimIndex           : Natural;
      EndOfMessageAttributesDelimIndex : Natural;
   begin
      This.Is_Valid := False;
      Result := False;

      --  endOfAddressDelimIndex = delimitedString.find(*(s_addressAttributesDelimiter().c_str()));
      EndOfAddressDelimIndex := Index (Source => Delimited_String, Pattern => Address_Attributes_Delimiter);

      --  if (endOfAddressDelimIndex == std::string::npos
      --     || endOfAddressDelimIndex > (delimitedString.length() - s_minimumDelimitedAddressAttributeMessageStringLength))
      if EndOfAddressDelimIndex = 0 or else
         EndOfAddressDelimIndex > Delimited_String'Length - Minimum_Delimited_Address_Attribute_Message_String_Length
      then
         return;
      end if;

      --  std::string::size_type endOfMessageAttributesDelimIndex = delimitedString.find(*(s_addressAttributesDelimiter().c_str()), (endOfAddressDelimIndex + 1));
      EndOfMessageAttributesDelimIndex := Index (Source  => Delimited_String,
                                                 Pattern => Address_Attributes_Delimiter,
                                                 From    => EndOfAddressDelimIndex + 1);
      --  if (endOfMessageAttributesDelimIndex == std::string::npos)
      if EndOfMessageAttributesDelimIndex = 0 then
         return;
      --  {
      --      UXAS_LOG_ERROR(s_typeName(), "::parseAddressedAttributedMessageStringAndSetFields failed to parse message attribute string from delimited string ", delimitedString);
      --      m_isValid = false;
      --      return (m_isValid);
      --  }
      --  else if (endOfMessageAttributesDelimIndex == (delimitedString.length() - 1))
      elsif EndOfMessageAttributesDelimIndex = Delimited_String'length then
      --  {
      --      UXAS_LOG_ERROR(s_typeName(), "::parseAddressedAttributedMessageStringAndSetFields payload must be non-empty");
      --      m_isValid = false;
      --      return (m_isValid);
         return;
      --  }
      end if;

      --  m_messageAttributes = uxas::stduxas::make_unique<MessageAttributes>();
      --  if (!m_messageAttributes->setAttributesFromDelimitedString(
      --      delimitedString.substr(endOfAddressDelimIndex + 1, endOfMessageAttributesDelimIndex - (endOfAddressDelimIndex + 1))))
      --  {
      --      UXAS_LOG_ERROR(s_typeName(), "::setAddressAttributesAndPayload failed to initialize message attributes");
      --      m_isValid = false;
      --      return (m_isValid);
      --  }
      This.Attributes := new Message_Attributes;
      This.Attributes.Set_Attributes_From_Delimited_String
        (Delimited_String (EndOfAddressDelimIndex + 1 .. EndOfMessageAttributesDelimIndex - 1),
         Result);
      if not Result then
         return;
      end if;

      --  m_address = delimitedString.substr(0, endOfAddressDelimIndex);
      Copy (Delimited_String (Delimited_String'First .. EndOfAddressDelimIndex - 1),
            To => This.Address);

      --  m_payload = delimitedString.substr(endOfMessageAttributesDelimIndex + 1, delimitedString.length() - (endOfMessageAttributesDelimIndex + 1));
      Copy (Delimited_String (EndOfMessageAttributesDelimIndex + 1 .. Delimited_String'last),
            To => This.Payload);

      Copy (Delimited_String, To => This.Content_String);

      Result := True;
      This.Is_Valid := True;
   end Parse_Addressed_Attributed_Message_String_And_Set_Fields;

end UxAS.Comms.Data.Addressed.Attributed;

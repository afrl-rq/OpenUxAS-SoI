--  see OpenUxAS\src\Communications\AddressedMessage.h

package UxAS.Comms.Data.Addressed is

   --     //address$payload
   --      uint32_t s_minimumDelimitedAddressMessageStringLength{3};
   Minimum_Delimited_Address_Message_String_Length : constant := 3;

   --  s_addressAttributesDelimiter character (must not be present within address)
   --  static std::string&
   --  s_addressAttributesDelimiter() { static std::string s_string("$"); return (s_string); };
   Address_Attributes_Delimiter : constant String := "$";

   --      static std::string&
   --      s_fieldDelimiter() { static std::string s_string("|"); return (s_string); };
   Field_Delimiter : constant String := "|";

   --     static bool
   --     isValidAddress(const std::string& address)
   function Is_Valid_Address (Address : String) return Boolean;

   --  static const std::string&
   --  s_typeName() { static std::string s_string("AddressedMessage"); return (s_string); };
   Type_Name : constant String := "AddressedMessage";

   type Addressed_Message is tagged limited private;

   type Addressed_Message_Ref  is access all Addressed_Message;
   type Addressed_Message_View is access constant Addressed_Message;
   type Any_Addressed_Message  is access Addressed_Message'Class;


   --  bool
   --  setAddressAndPayload(const std::string address, const std::string payload)
   procedure Set_Address_And_Payload
     (This    : in out Addressed_Message;
      Address : String;
      Payload : String;
      Result  : out Boolean)
   with Pre'Class =>
       Address'Length in 1 .. Address_Max_Length and then
       Payload'Length in 1 .. Payload_Max_Length;

   --  bool
   --  setAddressAndPayloadFromDelimitedString(const std::string delimitedString)
   procedure Set_Address_And_Payload_From_Delimited_String
     (This             : in out Addressed_Message;
      Delimited_String : String;
      Result           : out Boolean)
   with Pre'Class =>
       Delimited_String'Length >= Minimum_Delimited_Address_Message_String_Length;

   --  bool
   --  isValid()
   function Is_Valid (This : Addressed_Message) return Boolean;

   --      const std::string&
   --      getAddress() const
   --      {
   --          return m_address;
   --      };
   function Address (This : Addressed_Message) return String;

   --  Data payload to be transported.
   --      const std::string&
   --      getPayload() const
   --      {
   --          return m_payload;
   --      };
   function Payload (This : Addressed_Message) return String;

   --  Message address and payload combined into a single, delimited string.
   --       * @return Message string consisting of concatenated address and payload.
   --      virtual
   --      const std::string&
   --      getString() const
   function Content_String (This : Addressed_Message) return String;

private

   type Addressed_Message is tagged limited record
      Is_Valid       : Boolean := False;
      Content_String : Dynamic_String (Capacity => Content_String_Max_Length);      --  note different name (not m_string)
      Address        : Dynamic_String (Capacity => Address_Max_Length);
      Payload        : Dynamic_String (Capacity => Payload_Max_Length);
   end record;

   --  bool
   --  parseAddressedMessageStringAndSetFields(const std::string delimitedString)
   procedure Parse_Addressed_Message_String_And_Set_Fields
     (This             : in out Addressed_Message;
      Delimited_String : String;
      Result           : out Boolean);

end UxAS.Comms.Data.Addressed;

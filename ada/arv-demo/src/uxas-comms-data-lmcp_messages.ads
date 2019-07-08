--  see OpenUxAS\src\Communications\LmcpMessage.h

with AVTAS.LMCP.Object;

package UxAS.Comms.Data.LMCP_Messages is

   type LMCP_Message is tagged limited record
      --  these are public member data in the C++ version so they are visible
      --  in this base class (even if extensions are private, as they should be)

      --  Message attributes associated with the payload
      --  std::unique_ptr<MessageAttributes> m_attributes;
      Attributes : Message_Attributes_Ref;

      --  Data payload to be transported
      --  std::shared_ptr<avtas::lmcp::Object> m_object;
      Payload : AVTAS.LMCP.Object.Object_Any;
   end record;

   type LMCP_Message_Ref is access all LMCP_Message;
   type Any_LMCP_Message is access all LMCP_Message'Class;

   --  Ada: since the components are public we don't define a constructor function

end UxAS.Comms.Data.LMCP_Messages;

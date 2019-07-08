with UxAS.Common.Configuration_Manager;

package body UxAS.Comms.Transport.ZeroMQ_Sender.Addr_Attr_Msg_Senders is

   use ZMQ.Sockets;

   ------------------
   -- Send_Message --
   ------------------

   procedure Send_Message
     (This         : in out ZeroMq_Addressed_Attributed_Message_Sender;
      Address      : String;
      Content_Type : String;
      Descriptor   : String;
      Payload      : String)
   is
      --  uxas::communications::data::AddressedAttributedMessage message;
      Message : Addressed_Attributed_Message;
      Success : Boolean;
   begin
      --  message.setAddressAttributesAndPayload(address, contentType, descriptor, m_sourceGroup,
      --                                         m_entityIdString, m_serviceIdString, std::move(payload));
      Message.Set_Address_Attributes_And_Payload
        (Address           => Address,
         Content_Type      => Content_Type,
         Descriptor        => Descriptor,
         Source_Group      => Value (This.Source_Group),
         Source_Entity_Id  => Value (This.Entity_Id_String),
         Source_Service_Id => Value (This.Service_Id_String),
         Payload           => Payload,
         Result            => Success);

      if This.Kind = Stream then
         raise Program_Error with "Send_Message is not implemented for STREAM";
      else  -- not a stream socket
         if UxAS.Common.Configuration_Manager.Is_ZeroMq_Multipart_Message then
            raise Program_Error with "Send_Message is not implemented for multipart messages";
         else
            if Message.Is_Valid then
               This.ZMQ_Socket.Send (Message.Content_String);
            end if;
         end if;
      end if;
   end Send_Message;

   ---------------------------------------
   -- Send_Addressed_Attributed_Message --
   ---------------------------------------

   procedure Send_Addressed_Attributed_Message
     (This    : in out ZeroMq_Addressed_Attributed_Message_Sender;
      Message : Addressed_Attributed_Message_Ref)
   is
   begin
      if This.Kind = Stream then
         raise Program_Error with "Send_Addressed_Attributed_Message is not implemented for STREAM";
      else  -- not a stream socket
         if UxAS.Common.Configuration_Manager.Is_ZeroMq_Multipart_Message then
            raise Program_Error with "Send_Addressed_Attributed_Message is not implemented for multipart messages";
         else
            if Message.Is_Valid then
               This.ZMQ_Socket.Send (Message.Content_String);
            end if;
         end if;
      end if;
   end Send_Addressed_Attributed_Message;

end UxAS.Comms.Transport.ZeroMQ_Sender.Addr_Attr_Msg_Senders;

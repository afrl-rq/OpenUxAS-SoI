--  see OpenUxAS\src\Communications\ZeroMqAddressedAttributedMessageSender.h

with ZMQ.Sockets;
with UxAS.Comms.Data.Addressed.Attributed; use UxAS.Comms.Data.Addressed.Attributed;

package UxAS.Comms.Transport.ZeroMQ_Sender.Addr_Attr_Msg_Senders is

   type ZeroMq_Addressed_Attributed_Message_Sender (Kind : ZMQ.Sockets.Socket_Type) is
     new ZeroMq_Sender_Base with private;

   type ZeroMq_Addressed_Attributed_Message_Sender_Ref is access all ZeroMq_Addressed_Attributed_Message_Sender;

   type Any_ZeroMq_Addressed_Attributed_Message_Sender is access all ZeroMq_Addressed_Attributed_Message_Sender'Class;

   --  void
   --  sendMessage(const std::string& address, const std::string& contentType, const std::string& descriptor, const std::string payload);
   procedure Send_Message
     (This         : in out ZeroMq_Addressed_Attributed_Message_Sender;
      Address      : String;
      Content_Type : String;
      Descriptor   : String;
      Payload      : String);
   --  TODO: add preconditions on string lengths, as done elsewhere

   --  void
   --  sendAddressedAttributedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> message);
   procedure Send_Addressed_Attributed_Message
     (This    : in out ZeroMq_Addressed_Attributed_Message_Sender;
      Message : Addressed_Attributed_Message_Ref);

private

   type ZeroMq_Addressed_Attributed_Message_Sender (Kind : ZMQ.Sockets.Socket_Type) is
     new ZeroMq_Sender_Base with null record; -- by design

end UxAS.Comms.Transport.ZeroMQ_Sender.Addr_Attr_Msg_Senders;

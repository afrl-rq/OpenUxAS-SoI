with ZMQ.Messages;
with UxAS.Common.Configuration_Manager;

package body UxAS.Comms.Transport.Receiver.ZeroMQ.Addr_Attr_Msg_Receivers is

   ----------------
   -- Initialize --
   ----------------

   overriding
   procedure Initialize
     (This                 : in out ZeroMq_Addressed_Attributed_Message_Receiver;
      Entity_Id            : UInt32;
      Service_Id           : UInt32;
      Socket_Configuration : ZeroMq_Socket_Configuration)
   is
   begin
      Initialize
        (ZeroMq_Receiver_Base (This),  -- call parent version
         Entity_Id            => Entity_Id,
         Service_Id           => Service_Id,
         Socket_Configuration => Socket_Configuration);
      This.Is_Tcp_Stream := Socket_Configuration.Zmq_Socket_Type = Stream;
   end Initialize;

   use Message_Lists;

   function String_From_Socket (S : ZMQ.Sockets.Socket) return String;
   --  NOTE: s_recv() etc are defined in OpenUxAS\src\Utilities\UxAS_ZeroMQ.h
   --  as simple wrappers that hide result type conversions etc.

   ----------------------
   -- Get_Next_Message --
   ----------------------

   procedure Get_Next_Message
     (This : in out ZeroMq_Addressed_Attributed_Message_Receiver;
      Msg  : out Addressed_Attributed_Message_Ref)
   is
      --  std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> nextMsg;
   begin
      --  just send the next message if one is available
      if not Is_Empty (This.Received_Messages) then
         Msg := First_Element (This.Received_Messages);
         Delete_First (This.Received_Messages);
         return;
      end if;

      --  No messages in queue, attempt to read from socket.

      --  Polling is not supported in the current Ada binding to ZMQ (as of Feb
      --  2019), although we could do it with the low-level binding. Therefore
      --  we will use a blocking call (in function String_From_Socket). We
      --  don't need all the code below for our demo, since the demo doesn't
      --  use TcpStreams and the messages are not multipart.

      --  zmq::pollitem_t pollItems [] = {
      --     { *m_zmqSocket, 0, ZMQ_POLLIN, 0},
      --  };
      --
      --  zmq::poll(&pollItems[0], 1, uxas::common::ConfigurationManager::getZeroMqReceiveSocketPollWaitTime_ms()); // wait time units are milliseconds
      --
      --  if (pollItems[0].revents & ZMQ_POLLIN)  // polling detected received data
      --  {

      if This.Is_TCP_Stream then
         raise Program_Error with "Get_Next_Message is not implemented for STREAM";
      else  -- not a stream socket
         if UxAS.Common.Configuration_Manager.Is_ZeroMq_Multipart_Message then
            raise Program_Error with "Get_Next_Message is not implemented for multipart messages";
         else -- not a multipart message
            declare
               Recvd_Msg : Addressed_Attributed_Message_Ref;
               Success   : Boolean;
            begin
               --  std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> recvdSinglepartAddAttMsg
               --          = uxas::stduxas::make_unique<uxas::communications::data::AddressedAttributedMessage>();
               Recvd_Msg := new Addressed_Attributed_Message;

               --  if (recvdSinglepartAddAttMsg->setAddressAttributesAndPayloadFromDelimitedString(n_ZMQ::s_recv(*m_zmqSocket)))
               Recvd_Msg.Set_Address_Attributes_And_Payload_From_Delimited_String
                 (Delimited_String => String_From_Socket (This.Zmq_Socket),
                  Result           => Success);

               if Success then
                  --  if (m_entityIdString != recvdSinglepartAddAttMsg->getMessageAttributesReference()->getSourceEntityId()
                  --     || m_serviceIdString != recvdSinglepartAddAttMsg->getMessageAttributesReference()->getSourceServiceId())
                  if This.Entity_Id_String /= Recvd_Msg.Message_Attributes_Reference.Source_Entity_Id
                    or This.Service_Id_String /= Recvd_Msg.Message_Attributes_Reference.Source_Service_Id
                  then
                     --  m_recvdMsgs.push_back( std::move(recvdSinglepartAddAttMsg) );
                     Append (This.Received_Messages, Recvd_Msg);
                  end if;
               end if;
            end;
         end if;  --  is a multipart message
      end if;  -- is a stream socket

      --  now see if there was anything just put into the deque

      if not Is_Empty (This.Received_Messages) then
         Msg := First_Element (This.Received_Messages);
         Delete_First (This.Received_Messages);
      end if;
   end Get_Next_Message;

   ------------------------
   -- String_From_Socket --
   ------------------------

   function String_From_Socket (S : ZMQ.Sockets.Socket) return String is
      Message : ZMQ.Messages.Message;
   begin
      Message.Initialize (Size => 0);
      S.Recv (Message); -- blocking
      return Message.GetData;
   end String_From_Socket;

end UxAS.Comms.Transport.Receiver.ZeroMQ.Addr_Attr_Msg_Receivers;

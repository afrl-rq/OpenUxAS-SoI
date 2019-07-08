--  see OpenUxAS\src\Communications\LmcpObjectMessageSenderPipe.cpp

with UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;
with UxAS.Common.String_Constant.Lmcp_Network_Socket_Address;
use  UxAS.Common.String_Constant.Lmcp_Network_Socket_Address;
with UxAS.Common.String_Constant.Content_Type;
with UxAS.Comms.Transport.Network_Name;

with AVTAS.LMCP.Factory;
with AVTAS.LMCP.ByteBuffers;  use AVTAS.LMCP.ByteBuffers;

package body UxAS.Comms.LMCP_Object_Message_Sender_Pipes is

   ------------------------
   -- Initialize_Publish --
   ------------------------

   procedure Initialize_Publish
     (This         : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group : String;
      Entity_Id    : UInt32;
      Service_Id   : UInt32)
   is
   begin
      --  initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_PUB,
      --                      uxas::common::LmcpNetworkSocketAddress::strGetInProc_FromMessageHub(), true);
      This.Initialize_Zmq_Socket
        (Source_Group   => Source_Group,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.PUB,
         Socket_Address => InProc_From_MessageHub,
         Is_Server      => True);
   end Initialize_Publish;

   ------------------------------
   -- Initialize_External_Push --
   ------------------------------

   procedure Initialize_External_Push
     (This                    : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group            : String;
      Entity_Id               : UInt32;
      Service_Id              : UInt32;
      External_Socket_Address : String;
      Is_Server               : Boolean)
   is
   begin
      --  initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_PUSH, externalSocketAddress, isServer);
      This.Initialize_Zmq_Socket
        (Source_Group   => Source_Group,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.PUSH,
         Socket_Address => External_Socket_Address,
         Is_Server      => Is_Server);
   end Initialize_External_Push;

   -----------------------------
   -- Initialize_External_Pub --
   -----------------------------

   procedure Initialize_External_Pub
     (This                    : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group            : String;
      Entity_Id               : UInt32;
      Service_Id              : UInt32;
      External_Socket_Address : String;
      Is_Server               : Boolean)
   is
   begin
      --  initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_PUB, externalSocketAddress, isServer);
      This.Initialize_Zmq_Socket
        (Source_Group   => Source_Group,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.PUB,
         Socket_Address => External_Socket_Address,
         Is_Server      => Is_Server);
   end Initialize_External_Pub;

   ---------------------
   -- Initialize_Push --
   ---------------------

   procedure Initialize_Push
     (This         : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group : String;
      Entity_Id    : UInt32;
      Service_Id   : UInt32)
   is
   begin
      --  initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_PUSH,
      --                      uxas::common::LmcpNetworkSocketAddress::strGetInProc_ToMessageHub(), false);
      This.Initialize_Zmq_Socket
        (Source_Group   => Source_Group,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.PUSH,
         Socket_Address => InProc_To_MessageHub,
         Is_Server      => False);
   end Initialize_Push;

   -----------------------
   -- Initialize_Stream --
   -----------------------

   procedure Initialize_Stream
     (This           : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group   : String;
      Entity_Id      : UInt32;
      Service_Id     : UInt32;
      Socket_Address : String;
      Is_Server      : Boolean)
   is
   begin
      --  initializeZmqSocket(sourceGroup, entityId, serviceId, ZMQ_STREAM, socketAddress, isServer);
      This.Initialize_Zmq_Socket
        (Source_Group   => Source_Group,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.STREAM,
         Socket_Address => Socket_Address,
         Is_Server      => Is_Server);
   end Initialize_Stream;

   ----------------------------
   -- Send_Broadcast_Message --
   ----------------------------

   procedure Send_Broadcast_Message
     (This    : in out LMCP_Object_Message_Sender_Pipe;
      Message : AVTAS.LMCP.Object.Object_Any)
   is
   begin
      --  std::string fullLmcpObjectTypeName = lmcpObject->getFullLmcpTypeName();
      --  sendLimitedCastMessage(fullLmcpObjectTypeName, std::move(lmcpObject));
      This.Send_LimitedCast_Message (Message.getFullLmcpTypeName, Message);
   end Send_Broadcast_Message;

   ------------------------------
   -- Send_LimitedCast_Message --
   ------------------------------

   --   void
   --   sendLimitedCastMessage(const std::string& castAddress, std::unique_ptr<avtas::lmcp::Object> lmcpObject);
   procedure Send_LimitedCast_Message
     (This         : in out LMCP_Object_Message_Sender_Pipe;
      Cast_Address : String;
      Message      : AVTAS.LMCP.Object.Object_Any)
   is
      --  avtas::lmcp::ByteBuffer* lmcpByteBuffer = avtas::lmcp::Factory::packMessage(lmcpObject.get(), true);
      Buffer  : constant ByteBuffer := AVTAS.LMCP.Factory.PackMessage (Message, EnableChecksum => True);
      --  std::string serializedPayload = std::string(reinterpret_cast<char*>(lmcpByteBuffer->array()), lmcpByteBuffer->capacity());
      Payload : constant String := Buffer.Raw_Bytes;
   begin
      --  m_transportSender->sendMessage
      --   (castAddress,
      --    uxas::common::ContentType::lmcp(),
      --    lmcpObject->getFullLmcpTypeName(),
      --    std::move(serializedPayload));
      This.Sender.Send_Message
        (Address      => Cast_Address,
         Content_Type => UxAS.Common.String_Constant.Content_Type.Lmcp,
         Descriptor   => Message.getFullLmcpTypeName,
         Payload      => Payload);
   end Send_LimitedCast_Message;

   -----------------------------
   -- Send_Serialized_Message --
   -----------------------------

   procedure Send_Serialized_Message
     (This    : in out LMCP_Object_Message_Sender_Pipe;
      Message : Addressed_Attributed_Message_Ref)
   is
   begin
      --  m_transportSender->sendAddressedAttributedMessage(std::move(serializedLmcpObject));
      This.Sender.Send_Addressed_Attributed_Message (Message);
   end Send_Serialized_Message;

   -----------------------------------
   -- Send_Shared_Broadcast_Message --
   -----------------------------------

   procedure Send_Shared_Broadcast_Message
     (This    : in out LMCP_Object_Message_Sender_Pipe;
      Message : AVTAS.LMCP.Object.Object_Any)
   is
   begin
      --  sendSharedLimitedCastMessage(lmcpObject->getFullLmcpTypeName(), lmcpObject);
      This.Send_Shared_LimitedCast_Message (Message.getFullLmcpTypeName, Message);
   end Send_Shared_Broadcast_Message;

   -------------------------------------
   -- Send_Shared_LimitedCast_Message --
   -------------------------------------

   procedure Send_Shared_LimitedCast_Message
     (This         : in out LMCP_Object_Message_Sender_Pipe;
      Cast_Address : String;
      Message      : AVTAS.LMCP.Object.Object_Any)
   is
      --  avtas::lmcp::ByteBuffer* lmcpByteBuffer = avtas::lmcp::Factory::packMessage(lmcpObject.get(), true);
      Buffer  : constant ByteBuffer := AVTAS.LMCP.Factory.PackMessage (Message, EnableChecksum => True);
      --  std::string serializedPayload = std::string(reinterpret_cast<char*>(lmcpByteBuffer->array()), lmcpByteBuffer->capacity());
      Payload : constant String := Buffer.Raw_Bytes;
   begin
      --  Note: this body is identical to the body of Send_LimitedCast_Message, per the C++ implementation
      --  TODO: see why

      --  m_transportSender->sendMessage
      --   (castAddress,
      --    uxas::common::ContentType::lmcp(),
      --    lmcpObject->getFullLmcpTypeName(),
      --    std::move(serializedPayload));
      This.Sender.Send_Message
        (Address      => Cast_Address,
         Content_Type => UxAS.Common.String_Constant.Content_Type.Lmcp,
         Descriptor   => Message.getFullLmcpTypeName,
         Payload      => Payload);
   end Send_Shared_LimitedCast_Message;

   ---------------
   -- Entity_Id --
   ---------------

   function Entity_Id
     (This : LMCP_Object_Message_Sender_Pipe)
      return UInt32
   is (This.Entity_Id);

   ----------------
   -- Service_Id --
   ----------------

   function Service_Id
     (This : LMCP_Object_Message_Sender_Pipe)
      return UInt32
   is (This.Service_Id);

   -------------------
   -- Set_Entity_Id --
   -------------------

   procedure Set_Entity_Id
     (This  : in out LMCP_Object_Message_Sender_Pipe;
      Value : UInt32)
   is
   begin
      This.Entity_Id := Value;
   end Set_Entity_Id;

   --------------------
   -- Set_Service_Id --
   --------------------

   procedure Set_Service_Id
     (This  : in out LMCP_Object_Message_Sender_Pipe;
      Value : UInt32)
   is
   begin
      This.Service_Id := Value;
   end Set_Service_Id;

   ---------------------------
   -- Initialize_Zmq_Socket --
   ---------------------------

   procedure Initialize_Zmq_Socket
     (This           : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group   : String;
      Entity_Id      : UInt32;
      Service_Id     : UInt32;
      Zmq_SocketType : ZMQ.Sockets.Socket_Type;
      Socket_Address : String;
      Is_Server      : Boolean)
   is
      use UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;

      --  int32_t zmqhighWaterMark{100000};
      Zmq_High_Water_Mark : constant := 100_000;

      zmqLmcpNetworkSendSocket : ZeroMq_Socket_Configuration;
   begin
      --  m_entityId = entityId;
      --  m_serviceId = serviceId;
      This.Entity_Id := Entity_Id;
      This.Service_Id := Service_Id;

      --  uxas::communications::transport::ZeroMqSocketConfiguration
      --  zmqLmcpNetworkSendSocket(uxas::communications::transport::NETWORK_NAME::zmqLmcpNetwork(),
      --                           socketAddress,
      --                           zmqSocketType,
      --                           isServer,
      --                           false,
      --                           zmqhighWaterMark,
      --                           zmqhighWaterMark);
      ZmqLmcpNetworkSendSocket := Make
        (Network_Name            => UxAS.Comms.Transport.Network_Name.ZmqLmcpNetwork,
         Socket_Address          => Socket_Address,
         Is_Receive              => False,
         Zmq_Socket_Type         => Zmq_SocketType,
         Number_of_IO_Threads    => 1,
         Is_Server_Bind          => Is_Server,
         Receive_High_Water_Mark => Zmq_High_Water_Mark,
         Send_High_Water_Mark    => Zmq_High_Water_Mark);


      --  m_transportSender = uxas::stduxas::make_unique<uxas::communications::transport::ZeroMqAddressedAttributedMessageSender>(
      --          (zmqSocketType == ZMQ_STREAM ? true : false));
      This.Sender := new ZeroMq_Addressed_Attributed_Message_Sender (Zmq_SocketType);
      --  we just pass the actual socket type and let the sender do the test

      --  m_transportSender->initialize(sourceGroup, m_entityId, m_serviceId, zmqLmcpNetworkSendSocket);
      This.Sender.Initialize
        (Source_Group => Source_Group,
         Entity_Id    => Entity_Id,
         Service_Id   => Service_Id,
         SocketConfig => zmqLmcpNetworkSendSocket);
   end Initialize_Zmq_Socket;

end UxAS.Comms.LMCP_Object_Message_Sender_Pipes;

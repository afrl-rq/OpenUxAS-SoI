--  see OpenUxAS\src\Communications\LmcpObjectMessageSenderPipe.h

with AVTAS.LMCP.Object;
with UxAS.Comms.Data;
with UxAS.Comms.Data.Addressed.Attributed;
with UxAS.Comms.Transport.ZeroMQ_Sender.Addr_Attr_Msg_Senders;
with ZMQ.Sockets;

use UxAS.Comms.Data;
use UxAS.Comms.Transport.ZeroMQ_Sender.Addr_Attr_Msg_Senders;
use UxAS.Comms.Data.Addressed.Attributed;

package UxAS.Comms.LMCP_Object_Message_Sender_Pipes is

   type LMCP_Object_Message_Sender_Pipe is tagged limited private;

   --   void
   --   initializePublish(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId);
   procedure Initialize_Publish
     (This         : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group : String;
      Entity_Id    : UInt32;
      Service_Id   : UInt32);

   --   void
   --   initializeExternalPush(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId,
   --                           const std::string& externalSocketAddress, bool isServer);
   procedure Initialize_External_Push
     (This                    : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group            : String;
      Entity_Id               : UInt32;
      Service_Id              : UInt32;
      External_Socket_Address : String;
      Is_Server               : Boolean);

   --   void
   --   initializeExternalPub(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId,
   --                         const std::string& externalSocketAddress, bool isServer);
   procedure Initialize_External_Pub
     (This                    : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group            : String;
      Entity_Id               : UInt32;
      Service_Id              : UInt32;
      External_Socket_Address : String;
      Is_Server               : Boolean);

   --   void
   --   initializePush(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId);
   procedure Initialize_Push
     (This         : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group : String;
      Entity_Id    : UInt32;
      Service_Id   : UInt32);

   --   void
   --   initializeStream(const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId, const std::string& socketAddress, bool isServer);
   procedure Initialize_Stream
     (This           : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group   : String;
      Entity_Id      : UInt32;
      Service_Id     : UInt32;
      Socket_Address : String;
      Is_Server      : Boolean);

   --   void
   --   sendBroadcastMessage(std::unique_ptr<avtas::lmcp::Object> lmcpObject);
   procedure Send_Broadcast_Message
     (This    : in out LMCP_Object_Message_Sender_Pipe;
      Message : AVTAS.LMCP.Object.Object_Any);

   --   void
   --   sendLimitedCastMessage(const std::string& castAddress, std::unique_ptr<avtas::lmcp::Object> lmcpObject);
   procedure Send_LimitedCast_Message
     (This         : in out LMCP_Object_Message_Sender_Pipe;
      Cast_Address : String;
      Message      : AVTAS.LMCP.Object.Object_Any);

   --   void
   --   sendSerializedMessage(std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> serializedLmcpObject);
   procedure Send_Serialized_Message
     (This    : in out LMCP_Object_Message_Sender_Pipe;
      Message : Addressed_Attributed_Message_Ref);

   --   void
   --   sendSharedBroadcastMessage(const std::shared_ptr<avtas::lmcp::Object>& lmcpObject);
   procedure Send_Shared_Broadcast_Message
     (This    : in out LMCP_Object_Message_Sender_Pipe;
      Message : AVTAS.LMCP.Object.Object_Any);

   --   void
   --   sendSharedLimitedCastMessage(const std::string& castAddress, const std::shared_ptr<avtas::lmcp::Object>& lmcpObject);
   procedure Send_Shared_LimitedCast_Message
     (This         : in out LMCP_Object_Message_Sender_Pipe;
      Cast_Address : String;
      Message      : AVTAS.LMCP.Object.Object_Any);

   --  These attributes are public in the C++ version so we provide
   --  setters/getters rather than define the full ADT as a public tagged
   --  record type with the4se two components visible, combined with a
   --  component of a private type containing the private/protected members
   --
   --      uint32_t m_entityId;
   --      uint32_t m_serviceId;

   function Entity_Id  (This : LMCP_Object_Message_Sender_Pipe) return UInt32;
   function Service_Id (This : LMCP_Object_Message_Sender_Pipe) return UInt32;

   procedure Set_Entity_Id
     (This  : in out LMCP_Object_Message_Sender_Pipe;
      Value : UInt32);

   procedure Set_Service_Id
     (This  : in out LMCP_Object_Message_Sender_Pipe;
      Value : UInt32);

private

   type LMCP_Object_Message_Sender_Pipe is tagged limited record
      Entity_Id  : UInt32;
      Service_Id : UInt32;
      --  std::unique_ptr<uxas::communications::transport::ZeroMqAddressedAttributedMessageSender> m_transportSender;
      Sender     : ZeroMq_Addressed_Attributed_Message_Sender_Ref;
   end record;

   --     void
   --     initializeZmqSocket
   --        (const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId,
   --         int32_t zmqSocketType,
   --         const std::string& socketAddress,
   --         bool isServer);
   procedure Initialize_Zmq_Socket
     (This           : in out LMCP_Object_Message_Sender_Pipe;
      Source_Group   : String;
      Entity_Id      : UInt32;
      Service_Id     : UInt32;
      Zmq_SocketType : ZMQ.Sockets.Socket_Type;
      Socket_Address : String;
      Is_Server      : Boolean);

end UxAS.Comms.LMCP_Object_Message_Sender_Pipes;

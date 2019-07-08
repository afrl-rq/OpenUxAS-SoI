--  see OpenUxAS\src\Communications\LmcpObjectMessageReceiverPipe.h

with AVTAS.LMCP.Object;
with UxAS.Comms.Data.LMCP_Messages;
with UxAS.Comms.Data.Addressed.Attributed;
with UxAS.Comms.Transport.Receiver.ZeroMQ.Addr_Attr_Msg_Receivers;

use AVTAS.LMCP.Object;
use UxAS.Comms.Data.LMCP_Messages;
use UxAS.Comms.Data.Addressed.Attributed;
use UxAS.Comms.Transport.Receiver.ZeroMQ.Addr_Attr_Msg_Receivers;

package UxAS.Comms.LMCP_Object_Message_Receiver_Pipes is

   type LMCP_Object_Message_Receiver_Pipe is tagged limited private;

   --  void
   --  initializePull(uint32_t entityId, uint32_t serviceId);
   procedure Initialize_Pull
     (This       : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id  : UInt32;
      Service_Id : UInt32);

   --  void
   --  initializeExternalSubscription(uint32_t entityId, uint32_t serviceId, const std::string& externalSocketAddress, bool isServer);
   procedure Initialize_External_Subscription
     (This                    : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id               : UInt32;
      Service_Id              : UInt32;
      External_Socket_Address : String;
      Is_Server               : Boolean);

   --   void
   --   initializeExternalPull(uint32_t entityId, uint32_t serviceId, const std::string& externalSocketAddress, bool isServer);
   procedure Initialize_External_Pull
     (This                    : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id               : UInt32;
      Service_Id              : UInt32;
      External_Socket_Address : String;
      Is_Server               : Boolean);

   --   void
   --   initializeSubscription(uint32_t entityId, uint32_t serviceId);
   procedure Initialize_Subscription
     (This       : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id  : UInt32;
      Service_Id : UInt32);

   --   void
   --   initializeStream(uint32_t entityId, uint32_t serviceId, const std::string& socketAddress, bool isServer);
   procedure Initialize_Stream
     (This           : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id      : UInt32;
      Service_Id     : UInt32;
      Socket_Address : String;
      Is_Server      : Boolean);

   --   bool
   --   addLmcpObjectSubscriptionAddress(const std::string& address);
   procedure Add_Lmcp_Object_Subscription_Address
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Address : String;
      Result  : out Boolean);

   --   bool
   --   removeLmcpObjectSubscriptionAddress(const std::string& address);
   procedure Remove_Lmcp_Object_Subscription_Address
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Address : String;
      Result  : out Boolean);

   --   bool
   --   removeAllLmcpObjectSubscriptionAddresses();
   procedure Remove_All_Lmcp_Object_Subscription_Address
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Result  : out Boolean);

   --   std::unique_ptr<uxas::communications::data::LmcpMessage>
   --   getNextMessageObject();
   procedure Get_Next_Message_Object
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Message : out    Any_Lmcp_Message);

   --   std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>
   --   getNextSerializedMessage();
   procedure Get_Next_Serialized_Message
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Message : out    Addressed_Attributed_Message_Ref);

   --   std::unique_ptr<avtas::lmcp::Object>
   --   deserializeMessage(const std::string& payload);
   procedure Deserialize_Message
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Payload : String;
      Message : out not null AVTAS.LMCP.Object.Object_Any);

   --  These attributes are public in the C++ version so we provide getters
   --  (since that seems to be the need) rather than define the full ADT as a
   --  public tagged record type with the4se two components visible, combined
   --  with a component of a private type containing the private/protected
   --  members
   --
   --      uint32_t m_entityId;
   --      uint32_t m_serviceId;
   function Entity_Id  (This : LMCP_Object_Message_Receiver_Pipe) return UInt32;
   function Service_Id (This : LMCP_Object_Message_Receiver_Pipe) return UInt32;

private

   type LMCP_Object_Message_Receiver_Pipe is tagged limited record
      Entity_Id  : UInt32;
      Service_Id : UInt32;
      --    std::unique_ptr<uxas::communications::transport::ZeroMqAddressedAttributedMessageReceiver> m_transportReceiver;
      Receiver   : ZeroMq_Addressed_Attributed_Message_Receiver_Ref;
   end record;

end UxAS.Comms.LMCP_Object_Message_Receiver_Pipes;

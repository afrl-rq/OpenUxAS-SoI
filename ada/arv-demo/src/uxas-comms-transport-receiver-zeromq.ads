--  see OpenUxAS\src\Communications\ZeroMqReceiverBase.h

with ZMQ.Sockets;                                       use ZMQ.Sockets;
with UxAS.Comms.Transport.ZeroMQ_Socket_Configurations; use UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;

package UxAS.Comms.Transport.Receiver.ZeroMQ is

   type ZeroMq_Receiver_Base is abstract new Transport_Receiver_Base with private;

   --  Note: we don't implement the dtor

   --  void
   --  initialize(uint32_t entityId, uint32_t serviceId, SocketConfiguration& zeroMqSocketConfiguration);
   procedure Initialize
     (This                 : in out ZeroMq_Receiver_Base;
      Entity_Id            : UInt32;
      Service_Id           : UInt32;
      Socket_Configuration : ZeroMq_Socket_Configuration);  -- Note: not a reference. TODO: check this

   --  bool
   --  addSubscriptionAddressToSocket(const std::string& address) override;
   overriding
   procedure Add_Subscription_Address_To_Socket
     (This    : in out ZeroMq_Receiver_Base;
      Address : String;
      Result  : out Boolean);

   --  bool
   --  removeSubscriptionAddressFromSocket(const std::string& address) override;
   overriding
   procedure Remove_Subscription_Address_From_Socket
     (This    : in out ZeroMq_Receiver_Base;
      Address : String;
      Result  : out Boolean);

private

   type ZeroMq_Receiver_Base is new Transport_Receiver_Base with record
      Entity_Id_String     : Dynamic_String (Capacity => Entity_Id_String_Max_Length);
      Service_Id_String    : Dynamic_String (Capacity => Service_Id_String_Max_Length);
      Socket_Configuration : ZeroMq_Socket_Configuration;
      --  std::unique_ptr<zmq::socket_t> m_zmqSocket;
      Zmq_Socket           : ZMQ.Sockets.Socket;                 --  NOTE: not a pointer (TODO: change??)
   end record;

end UxAS.Comms.Transport.Receiver.ZeroMQ;

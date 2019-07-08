--  see OpenUxAS\src\Communications\ZeroMqSenderBase.h

with UxAS.Comms.Transport.ZeroMQ_Socket_Configurations; use UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;
with ZMQ.Sockets;

package UxAS.Comms.Transport.ZeroMQ_Sender is

   type ZeroMq_Sender_Base is new Transport_Base with private;

   --  void
   --  initialize (const std::string& sourceGroup, uint32_t entityId, uint32_t serviceId, SocketConfiguration& zeroMqSocketConfiguration);
   procedure Initialize
     (This         : in out ZeroMq_Sender_Base;
      Source_Group : String;
      Entity_Id    : UInt32;
      Service_Id   : UInt32;
      SocketConfig : ZeroMq_Socket_Configuration)
     with
       Pre'Class => Source_Group'Length <= Source_Group_Max_Length;

private

   type ZeroMq_Sender_Base is new Transport_Base with record
      --  std::string m_sourceGroup;
      Source_Group : Dynamic_String (Source_Group_Max_Length);
      --  std::string m_entityIdString;
      Entity_Id_String : Dynamic_String (Entity_Id_Max_Length);
      --  std::string m_serviceIdString;
      Service_Id_String : Dynamic_String (Service_Id_String_Max_Length);
      --  ZeroMqSocketConfiguration m_zeroMqSocketConfiguration;
      ZMQ_Socket_Config : ZeroMq_Socket_Configuration;
      --  std::unique_ptr<zmq::socket_t> m_zmqSocket;
      ZMQ_Socket : ZMQ.Sockets.Socket;
   end record;

end UxAS.Comms.Transport.ZeroMQ_Sender;

with UxAS.Comms.Transport.ZeroMQ_Fabric;  use UxAS.Comms.Transport;
with String_Utils;                        use String_Utils;

package body UxAS.Comms.Transport.Receiver.ZeroMQ is

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize
     (This                 : in out ZeroMq_Receiver_Base;
      Entity_Id            : UInt32;
      Service_Id           : UInt32;
      Socket_Configuration : ZeroMq_Socket_Configuration)
   is
   begin
      --  m_entityId = entityId;
      This.Entity_Id := Entity_Id;
      --  m_serviceId = serviceId;
      This.Service_Id := Service_Id;
      --  m_entityIdString = std::to_string(entityId);
      Copy (To_String (Entity_Id), To => This.Entity_Id_String);
      --  m_serviceIdString = std::to_string(serviceId);
      Copy (To_String (Service_Id), To => This.Service_Id_String);

      --  m_zeroMqSocketConfiguration = static_cast<ZeroMqSocketConfiguration&> (zeroMqSocketConfiguration);
      This.Socket_Configuration := Initialize.Socket_Configuration;

      --  m_zmqSocket = ZeroMqFabric::getInstance().createSocket(m_zeroMqSocketConfiguration);
      ZeroMQ_Fabric.Create_Socket
        (ZeroMQ_Fabric.Instance,
         Config => This.Socket_Configuration,
         Result => This.Zmq_Socket);
   end Initialize;

   ----------------------------------------
   -- Add_Subscription_Address_To_Socket --
   ----------------------------------------

   overriding
   procedure Add_Subscription_Address_To_Socket
     (This    : in out ZeroMq_Receiver_Base;
      Address : String;
      Result  : out Boolean)
   is
   begin
      --  bool isAdded(false);
      --  if (m_zeroMqSocketConfiguration.m_zmqSocketType == ZMQ_SUB)
      --  {
      --     m_zmqSocket->setsockopt(ZMQ_SUBSCRIBE, address.c_str(), address.size());
      --     isAdded = true;
      --  }
      --  return (isAdded);
      if This.Socket_Configuration.Zmq_Socket_Type = ZMQ.Sockets.SUB then
         This.Zmq_Socket.Establish_Message_Filter (Value => Address);
         Result := True;
      else
         Result := False;
      end if;
   end Add_Subscription_Address_To_Socket;

   ---------------------------------------------
   -- Remove_Subscription_Address_From_Socket --
   ---------------------------------------------

   overriding
   procedure Remove_Subscription_Address_From_Socket
     (This    : in out ZeroMq_Receiver_Base;
      Address : String;
      Result  : out Boolean)
   is
   begin
      --  bool isRemoved(false);
      --  if (m_zeroMqSocketConfiguration.m_zmqSocketType == ZMQ_SUB)
      --  {
      --      m_zmqSocket->setsockopt(ZMQ_UNSUBSCRIBE, address.c_str(), address.size());
      --      isRemoved = true;
      --  }
      --  return (isRemoved);
      if This.Socket_Configuration.Zmq_Socket_Type = ZMQ.Sockets.SUB then
         This.Zmq_Socket.Remove_Message_Filter (Value => Address);
         Result := True;
      else
         Result := False;
      end if;
   end Remove_Subscription_Address_From_Socket;

end UxAS.Comms.Transport.Receiver.ZeroMQ;

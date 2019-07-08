with String_Utils;  use String_Utils;

with UxAS.Comms.Transport.ZeroMQ_Fabric; use UxAS.Comms.Transport;

package body UxAS.Comms.Transport.ZeroMQ_Sender is

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize
     (This         : in out ZeroMq_Sender_Base;
      Source_Group : String;
      Entity_Id    : UInt32;
      Service_Id   : UInt32;
      SocketConfig : ZeroMq_Socket_Configuration)
   is
   begin
      --      m_sourceGroup = sourceGroup;
      Copy (Source_Group, To => This.Source_Group);
      --      m_entityId = entityId;
      This.Entity_Id := Entity_Id;
      --      m_serviceId = serviceId;
      This.Service_Id := Service_Id;
      --      m_entityIdString = std::to_string(entityId);
      Copy (To_String (Entity_Id), To => This.Entity_Id_String);

      --      m_serviceIdString = std::to_string(serviceId);
      Copy (To_String (Service_Id), To => This.Service_Id_String);

      --      m_zeroMqSocketConfiguration = static_cast<ZeroMqSocketConfiguration&> (zeroMqSocketConfiguration);
      This.ZMQ_Socket_Config := SocketConfig;
      --  TODO: check the above...!

      --  m_zmqSocket = ZeroMqFabric::getInstance().createSocket(m_zeroMqSocketConfiguration);
      ZeroMQ_Fabric.Create_Socket (This   => ZeroMQ_Fabric.Instance,
                                   Config => This.ZMQ_Socket_Config,
                                   Result => This.ZMQ_Socket);
   end Initialize;

end UxAS.Comms.Transport.ZeroMQ_Sender;

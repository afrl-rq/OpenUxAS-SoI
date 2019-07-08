with Ada.Unchecked_Deallocation;

package body UxAS.Comms.Transport.ZeroMQ_Fabric is

   procedure Free is new Ada.Unchecked_Deallocation (ZMQ_Fabric, ZMQ_Fabric_Reference);

   --------------
   -- Instance --
   --------------

   function Instance return not null ZMQ_Fabric_Reference is
   begin
      if The_Instance = null then
         The_Instance := new ZMQ_Fabric;
      end if;
      return The_Instance;
   end Instance;

   -------------
   -- Destroy --
   -------------

   procedure Destroy is
   begin
      Free (The_Instance);
   end Destroy;

   -------------------
   -- Create_Socket --
   -------------------

   procedure Create_Socket
     (This   : ZMQ_Fabric_Reference;
      Config : ZeroMq_Socket_Configuration;
      Result : out Socket)
   is
   begin
      This.zmQContext.Set_Number_Of_IO_Threads (Config.Number_of_IO_Threads);

      --  std::unique_ptr<zmq::socket_t> zmqSocket = uxas::stduxas::make_unique<zmq::socket_t>(*m_zmqContext, socketConfiguration.m_zmqSocketType);
      ZMQ.Sockets.Initialize (Result, This.zmQContext, Config.Zmq_Socket_Type);

      if Config.Is_Server_Bind then
         Result.Bind (Address =>  Value (Config.Socket_Address));
      else
         Result.Connect (Address => Value (Config.Socket_Address));
      end if;

      --  zmqSocket->setsockopt(ZMQ_RCVHWM, &socketConfiguration.m_receiveHighWaterMark, sizeof (socketConfiguration.m_receiveHighWaterMark));
      Result.Set_High_Water_Mark_For_Inbound_Messages (Integer (Config.Receive_High_Water_Mark));

      --  zmqSocket->setsockopt(ZMQ_SNDHWM, &socketConfiguration.m_sendHighWaterMark, sizeof (socketConfiguration.m_sendHighWaterMark));
      Result.Set_High_Water_Mark_For_Outbound_Messages (Integer (Config.Send_High_Water_Mark));
   end Create_Socket;

end UxAS.Comms.Transport.ZeroMQ_Fabric;

-- see OpenUxAS\src\Communications\ZeroMqFabric.h

with UxAS.Comms.Transport.ZeroMQ_Socket_Configurations; use UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;
with ZMQ.Sockets;  use ZMQ.Sockets;
with ZMQ.Contexts; use ZMQ.Contexts;

package UxAS.Comms.Transport.ZeroMQ_Fabric is

   type ZMQ_Fabric (<>) is tagged limited private;

   type Any_Manager is access all ZMQ_Fabric'Class;

   type ZMQ_Fabric_Reference is access all ZMQ_Fabric;

   function Instance return not null ZMQ_Fabric_Reference;

   procedure Destroy;

   --  TODO: the C++ version uses pointers to the context and result
   --
   --  std::unique_ptr<zmq::socket_t>
   --  createSocket(ZeroMqSocketConfiguration& socketConfiguration);
   procedure Create_Socket
     (This   : ZMQ_Fabric_Reference;
      Config : ZeroMq_Socket_Configuration;
      Result : out Socket);

private

   type ZMQ_Fabric is tagged limited record
      --  std::unique_ptr<zmq::context_t> m_zmqContext;
      zmQContext : Context;
   end record;

   The_Instance : ZMQ_Fabric_Reference;
   --  we use lazy allocation...

end UxAS.Comms.Transport.ZeroMQ_Fabric;

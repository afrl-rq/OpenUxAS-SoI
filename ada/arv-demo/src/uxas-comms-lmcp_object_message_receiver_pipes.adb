with ZMQ.Sockets;
with AVTAS.LMCP.Factory;

with UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;
use  UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;

with UxAS.Comms.Transport.Network_Name;

with UxAS.Common.String_Constant.Lmcp_Network_Socket_Address;
use  UxAS.Common.String_Constant.Lmcp_Network_Socket_Address;

with AVTAS.LMCP.ByteBuffers;   use AVTAS.LMCP.ByteBuffers;

package body UxAS.Comms.LMCP_Object_Message_Receiver_Pipes is

   procedure Initialize_Zmq_Socket
     (This           : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id      : UInt32;
      Service_Id     : UInt32;
      Zmq_SocketType : ZMQ.Sockets.Socket_Type;
      Socket_Address : String;
      Is_Server      : Boolean);

   ---------------------
   -- Initialize_Pull --
   ---------------------

   procedure Initialize_Pull
     (This       : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id  : UInt32;
      Service_Id : UInt32)
   is
   begin
      Initialize_Zmq_Socket
        (This,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.PULL,
         Socket_Address => InProc_To_MessageHub,
         Is_Server      => True);
   end Initialize_Pull;

   --------------------------------------
   -- Initialize_External_Subscription --
   --------------------------------------

   procedure Initialize_External_Subscription
     (This                    : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id               : UInt32;
      Service_Id              : UInt32;
      External_Socket_Address : String;
      Is_Server               : Boolean)
   is
   begin
      Initialize_Zmq_Socket
        (This,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.SUB,
         Socket_Address => External_Socket_Address,
         Is_Server      => Is_Server);
   end Initialize_External_Subscription;

   ------------------------------
   -- Initialize_External_Pull --
   ------------------------------

   procedure Initialize_External_Pull
     (This                    : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id               : UInt32;
      Service_Id              : UInt32;
      External_Socket_Address : String;
      Is_Server               : Boolean)
   is
   begin
      Initialize_Zmq_Socket
        (This,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.PULL,
         Socket_Address => External_Socket_Address,
         Is_Server      => Is_Server);
   end Initialize_External_Pull;

   -----------------------------
   -- Initialize_Subscription --
   -----------------------------

   procedure Initialize_Subscription
     (This       : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id  : UInt32;
      Service_Id : UInt32)
   is
   begin
      Initialize_Zmq_Socket
        (This,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.SUB,
         Socket_Address => InProc_From_MessageHub,
         Is_Server      => False);
   end Initialize_Subscription;

   -----------------------
   -- Initialize_Stream --
   -----------------------

   procedure Initialize_Stream
     (This           : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id      : UInt32;
      Service_Id     : UInt32;
      Socket_Address : String;
      Is_Server      : Boolean)
   is
   begin
      Initialize_Zmq_Socket
        (This,
         Entity_Id      => Entity_Id,
         Service_Id     => Service_Id,
         Zmq_SocketType => ZMQ.Sockets.STREAM,
         Socket_Address => Socket_Address,
         Is_Server      => Is_Server);
   end Initialize_Stream;

   ------------------------------------------
   -- Add_Lmcp_Object_Subscription_Address --
   ------------------------------------------

   procedure Add_Lmcp_Object_Subscription_Address
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Address : String;
      Result  : out Boolean)
   is
   begin
      This.Receiver.Add_Subscription_Address (Address, Result);
   end Add_Lmcp_Object_Subscription_Address;

   ---------------------------------------------
   -- Remove_Lmcp_Object_Subscription_Address --
   ---------------------------------------------

   procedure Remove_Lmcp_Object_Subscription_Address
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Address : String;
      Result  : out Boolean)
   is
   begin
      This.Receiver.Remove_Subscription_Address (Address, Result);
   end Remove_Lmcp_Object_Subscription_Address;

   -------------------------------------------------
   -- Remove_All_Lmcp_Object_Subscription_Address --
   -------------------------------------------------

   procedure Remove_All_Lmcp_Object_Subscription_Address
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Result  : out Boolean)
   is
   begin
      This.Receiver.Remove_All_Subscription_Addresses (Result);
   end Remove_All_Lmcp_Object_Subscription_Address;

   -----------------------------
   -- Get_Next_Message_Object --
   -----------------------------

   procedure Get_Next_Message_Object
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Message : out    Any_Lmcp_Message)
   is
      Next_Message : Addressed_Attributed_Message_Ref;
      Object       : AVTAS.LMCP.Object.Object_Any;
   begin
      This.Receiver.Get_Next_Message (Next_Message);
      if Next_Message /= null then
         Deserialize_Message (This, Next_Message.Payload, Object);
         if Object /= null then
            Message := new LMCP_Message'(Attributes => Next_Message.Message_Attributes_Ownership,
                                         Payload    => Object);
         else
            Message := null;
         end if;
      else
         Message := null;
      end if;
   end Get_Next_Message_Object;

   ---------------------------------
   -- Get_Next_Serialized_Message --
   ---------------------------------

   procedure Get_Next_Serialized_Message
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Message : out    Addressed_Attributed_Message_Ref)
   is
   begin
      This.Receiver.Get_Next_Message (Message);
   end Get_Next_Serialized_Message;

   -------------------------
   -- Deserialize_Message --
   -------------------------

   procedure Deserialize_Message
     (This    : in out LMCP_Object_Message_Receiver_Pipe;
      Payload : String;
      Message : out not null AVTAS.LMCP.Object.Object_Any)
   is
      pragma Unreferenced (This);
      Buffer : ByteBuffer (Payload'Length);
   begin
      Buffer.Put_Raw_Bytes (Payload);
      Buffer.Rewind;

      AVTAS.LMCP.Factory.GetObject (Buffer, Message);
   end Deserialize_Message;

   ---------------
   -- Entity_Id --
   ---------------

   function Entity_Id (This : LMCP_Object_Message_Receiver_Pipe) return UInt32 is
      (This.Entity_Id);

   ----------------
   -- Service_Id --
   ----------------

   function Service_Id (This : LMCP_Object_Message_Receiver_Pipe) return UInt32 is
      (This.Service_Id);

   ---------------------------
   -- Initialize_Zmq_Socket --
   ---------------------------

   procedure Initialize_Zmq_Socket
     (This           : in out LMCP_Object_Message_Receiver_Pipe;
      Entity_Id      : UInt32;
      Service_Id     : UInt32;
      Zmq_SocketType : ZMQ.Sockets.Socket_Type;
      Socket_Address : String;
      Is_Server      : Boolean)
   is
      Zmq_High_Water_Mark : constant Int32 := 100_000;

      Configuration : constant ZeroMq_Socket_Configuration := Make
        (Network_Name            => UxAS.Comms.Transport.Network_Name.ZmqLmcpNetwork,
         Socket_Address          => Socket_Address,
         Zmq_Socket_Type         => Zmq_SocketType,
         Number_of_IO_Threads    => 1,
         Is_Server_Bind          => Is_Server,
         Is_Receive              => True,
         Receive_High_Water_Mark => Zmq_High_Water_Mark,
         Send_High_Water_Mark    => Zmq_High_Water_Mark);

   begin
      This.Entity_Id := Entity_Id;
      This.Service_Id := Service_Id;
      This.Receiver := new ZeroMq_Addressed_Attributed_Message_Receiver;
      This.Receiver.Initialize (Entity_Id, Service_Id, Configuration);
   end Initialize_Zmq_Socket;

end UxAS.Comms.LMCP_Object_Message_Receiver_Pipes;

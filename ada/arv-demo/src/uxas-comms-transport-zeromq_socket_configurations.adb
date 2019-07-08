package body UxAS.Comms.Transport.ZeroMQ_Socket_Configurations is

   ----------
   -- Make --
   ----------

   function Make
     (Network_Name            : String;
      Socket_Address          : String;
      Is_Receive              : Boolean;
      Zmq_Socket_Type         : ZMQ.Sockets.Socket_Type;
      Number_Of_IO_Threads    : Positive;
      Is_Server_Bind          : Boolean;
      Receive_High_Water_Mark : Int32;
      Send_High_Water_Mark    : Int32)
   return ZeroMq_Socket_Configuration
   is
      Result : ZeroMq_Socket_Configuration;
   begin
      Result.Is_Receive := Is_Receive;
      Copy (Network_Name,   To => Result.Network_Name);
      Copy (Socket_Address, To => Result.Socket_Address);

      Result.Zmq_Socket_Type := Zmq_Socket_Type;
      Result.Number_of_IO_Threads := Number_Of_IO_Threads;
      Result.Is_Server_Bind := Is_Server_Bind;
      Result.Receive_High_Water_Mark := Receive_High_Water_Mark;
      Result.Send_High_Water_Mark := Send_High_Water_Mark;
      return Result;
   end Make;

end UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;

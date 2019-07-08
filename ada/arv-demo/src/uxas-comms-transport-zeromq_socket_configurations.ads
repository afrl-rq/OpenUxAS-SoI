with UxAS.Comms.Transport.Socket_Configurations;
use UxAS.Comms.Transport.Socket_Configurations;

with ZMQ.Sockets;

package UxAS.Comms.Transport.ZeroMQ_Socket_Configurations is

   type ZeroMq_Socket_Configuration is new Socket_Configuration with record
      Zmq_Socket_Type         : ZMQ.Sockets.Socket_Type;
      Is_Server_Bind          : Boolean;
      Receive_High_Water_Mark : Int32;
      Send_High_Water_Mark    : Int32;
      Number_of_IO_Threads    : Positive;
   end record;

   function Make  -- a convenience routine
     (Network_Name            : String;
      Socket_Address          : String;
      Is_Receive              : Boolean;
      Zmq_Socket_Type         : ZMQ.Sockets.Socket_Type;
      Number_of_IO_Threads    : Positive;
      Is_Server_Bind          : Boolean;
      Receive_High_Water_Mark : Int32;
      Send_High_Water_Mark    : Int32)
   return ZeroMq_Socket_Configuration
   with Pre'Class =>
      Network_Name'Length   in 1 .. Max_Network_Name_Length and then
      Socket_Address'Length in 1 .. Max_Socket_Address_Length;

end UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;

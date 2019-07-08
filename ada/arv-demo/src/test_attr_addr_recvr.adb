with ZMQ.Sockets;

with Ada.Text_IO;  use Ada.Text_IO;

with AVTAS.LMCP.Types;                                              use AVTAS.LMCP.Types;
with UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;             use UxAS.Comms.Transport.ZeroMQ_Socket_Configurations;
with UxAS.Comms.Data.Addressed.Attributed;                          use UxAS.Comms.Data.Addressed.Attributed;
with UxAS.Comms.Transport.Receiver.ZeroMQ.Addr_Attr_Msg_Receivers ; use UxAS.Comms.Transport.Receiver.ZeroMQ.Addr_Attr_Msg_Receivers ;
with UxAS.Comms.Data;                                               use UxAS.Comms.Data;

use UxAS.Comms.Transport.Receiver;

procedure Test_Attr_Addr_Recvr is

   Receiver : ZeroMq_Addressed_Attributed_Message_Receiver;

   Msg : Addressed_Attributed_Message_Ref;

   Config : ZeroMq_Socket_Configuration;

   Success : Boolean;

   Max_Payload_Measured : Natural := 0;

begin
   Config := Make
     (Network_Name            => "unspecified",
      Socket_Address          => "tcp://127.0.0.1:5560",
      Is_Receive              => True,
      Zmq_Socket_Type         => ZMQ.Sockets.SUB,
      Number_of_IO_Threads    => 1,
      Is_Server_Bind          => False,
      Receive_High_Water_Mark => 10_000,
      Send_High_Water_Mark    => 10_000);

   Receiver.Initialize
     (Entity_Id            => 0,  -- don't use 100, that's the sender's
      Service_Id           => 0,  -- don't use 60, that's the sender's
      Socket_Configuration => Config);

   Receiver.Add_Subscription_Address (Any_Address_Accepted, Success);
   if not Success then
      Put_Line ("Could not add subscription address to Receiver");
      return;
   end if;

   loop
      Receiver.Get_Next_Message (Msg);  -- blocking
      if Msg = null then
         Put_Line ("Receiver got null msg pointer");
      else
         declare
            Msg_Attr : Message_Attributes_View renames Message_Attributes_Reference (Msg.all);
         begin
            Put_Line ("Address              : "  & Msg.Address);
            Put_Line ("Payload_Content_Type : "  & Msg_Attr.Payload_Content_Type);
            Put_Line ("Payload_Descriptor   : "  & Msg_Attr.Payload_Descriptor);
            Put_Line ("Source_Group         : "  & Msg_Attr.Source_Group);
            Put_Line ("Source_Entity_Id     : "  & Msg_Attr.Source_Entity_Id);
            Put_Line ("Source_Service_Id    : "  & Msg_Attr.Source_Service_Id);
            Put_Line ("Payload length       :"   & Msg.Payload'Length'Image);

            if Msg.Payload'Length > Max_Payload_Measured then
               Max_Payload_Measured := Msg.Payload'Length;
            end if;
            Put_Line ("Max_Payload_Measured :"   & Max_Payload_Measured'Image);

            New_Line;
         end;

         delay 0.5; -- just to give time to read it
      end if;
   end loop;
end Test_Attr_Addr_Recvr;

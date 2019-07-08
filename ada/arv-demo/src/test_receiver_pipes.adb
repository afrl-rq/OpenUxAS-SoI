with Ada.Text_IO;  use Ada.Text_IO;

with AVTAS.LMCP.Types;                              use AVTAS.LMCP.Types;
with UxAS.Comms.Data;                               use UxAS.Comms.Data;
with UxAS.Comms.Transport.Receiver;                 use UxAS.Comms.Transport.Receiver;
with UxAS.Comms.LMCP_Object_Message_Receiver_Pipes; use UxAS.Comms.LMCP_Object_Message_Receiver_Pipes;
with UxAS.Comms.Data.LMCP_Messages;                 use UxAS.Comms.Data.LMCP_Messages;
with Avtas.Lmcp.Object;

procedure Test_Receiver_Pipes is
   Receiver : LMCP_Object_Message_Receiver_Pipe;
   Msg      : Any_Lmcp_Message;
   Success  : Boolean;
begin
   Receiver.Initialize_External_Subscription
     (Entity_Id               => 200,
      Service_Id              => 0,
      External_Socket_Address => "tcp://127.0.0.1:5560",
      Is_Server               => False);

   Receiver.Add_Lmcp_Object_Subscription_Address (Any_Address_Accepted, Success);
   if not Success then
      Put_Line ("Could not add subscription address to Receiver");
      return;
   end if;

   loop
      Receiver.Get_Next_Message_Object (Msg);
      if Msg = null then
         Put_Line ("Receiver got null msg pointer!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
      else
         Put_Line ("LMCP Type Name       : " & Msg.Payload.getLmcpTypeName);
         Put_Line ("Full LMCP Type Name  : " & Msg.Payload.getFullLmcpTypeName);
         Put_Line ("LMCP Type            :"  & Msg.Payload.getLmcpType'Image);
         Put_Line ("Series Name          : " & Msg.Payload.getSeriesName);
         Put_Line ("Series Version       :"  & Msg.Payload.getSeriesVersion'Image);

         Put_Line ("Payload_Content_Type : " & Msg.Attributes.Payload_Content_Type);
         Put_Line ("Payload_Descriptor   : " & Msg.Attributes.Payload_Descriptor);
         Put_Line ("Source_Group         : " & Msg.Attributes.Source_Group);
         Put_Line ("Source_Entity_Id     : " & Msg.Attributes.Source_Entity_Id);
         Put_Line ("Source_Service_Id    : " & Msg.Attributes.Source_Service_Id);

         New_Line;
      end if;
   end loop;
end Test_Receiver_Pipes;

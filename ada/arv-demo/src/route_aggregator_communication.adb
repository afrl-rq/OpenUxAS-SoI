with AVTAS.LMCP.Types;
with UxAS.Common.String_Constant.Message_Group;
with Route_Aggregator_Message_Conversions; use Route_Aggregator_Message_Conversions;

package body Route_Aggregator_Communication is

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize
     (This         : out Route_Aggregator_Mailbox;
      Source_Group : String;
      Unique_Id    : Int64;
      Entity_Id    : UInt32;
      Service_Id   : UInt32)
   is
   begin
      --  The procedure UxAS.Comms.LMCP_Net_Client.Initialize_Network_Client()
      --  will also initialize its Message_Sender_Pipe component but will not
      --  use it for sending:
      --
      --  This.Message_Sender_Pipe.Initialize_Push
      --    (Source_Group => Value (This.Message_Source_Group),
      --     Entity_Id    => This.Entity_Id,
      --     Service_Id   => UInt32 (This.Network_Id));

      This.Message_Sender_Pipe.Initialize_Push
        (Source_Group => Source_Group,
         Entity_Id    => AVTAS.LMCP.Types.UInt32 (Entity_Id),
         Service_Id   => AVTAS.LMCP.Types.UInt32 (Service_Id));

      This.Unique_Entity_Send_Message_Id := Unique_Id;
   end Initialize;

   ----------------------------------------
   -- Get_Next_Unique_Sending_Message_Id --
   ----------------------------------------

   procedure Get_Next_Unique_Sending_Message_Id
     (This  : in out Route_Aggregator_Mailbox;
      Value : out Int64)
   is
   begin
      This.Unique_Entity_Send_Message_Id := This.Unique_Entity_Send_Message_Id + 1;
      Value := This.Unique_Entity_Send_Message_Id;
   end Get_Next_Unique_Sending_Message_Id;

   ----------------------------
   -- sendLimitedCastMessage --
   ----------------------------

   --  this is sendSharedLmcpObjectLimitedCastMessage(), in our code Send_Shared_LMCP_Object_Limited_Cast_Message

   procedure SendLimitedCastMessage
     (This  : in out Route_Aggregator_Mailbox;
      Group : MessageGroup;
      Msg   : Message_Root'Class)
   is
      use UxAS.Common.String_Constant;
   begin
      This.Unique_Entity_Send_Message_Id := This.Unique_Entity_Send_Message_Id + 1;
      --  This.Message_Sender_Pipe.Send_Shared_LimitedCast_Message (Cast_Address, Msg);
      This.Message_Sender_Pipe.Send_Shared_LimitedCast_Message
        (Cast_Address => (case Group is
                          when GroundPathPlanner   => Message_Group.GroundPathPlanner,
                          when AircraftPathPlanner => Message_Group.AircraftPathPlanner),
         Message      => As_Object_Any (Msg));
   end sendLimitedCastMessage;

   --------------------------
   -- sendBroadcastMessage --
   --------------------------

   --  this is sendSharedLmcpObjectBroadcastMessage(), in our code Send_Shared_LMCP_Object_Broadcast_Message

   procedure SendBroadcastMessage
     (This : in out Route_Aggregator_Mailbox;
      Msg  : Message_Root'Class)
   is
   begin
      This.Unique_Entity_Send_Message_Id := This.Unique_Entity_Send_Message_Id + 1;
      --  This.Message_Sender_Pipe.Send_Shared_Broadcast_Message (Msg);
      This.Message_Sender_Pipe.Send_Shared_Broadcast_Message (As_Object_Any (Msg));
   end sendBroadcastMessage;

end Route_Aggregator_Communication;

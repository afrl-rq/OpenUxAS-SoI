package body Route_Aggregator_Communication is

   ----------------------------
   -- sendLimitedCastMessage --
   ----------------------------

   procedure sendLimitedCastMessage
     (This  : in out Route_Aggregator_Mailbox;
      Group : MessageGroup;
      Msg   : Message_Root'Class)
   is
   begin
      pragma Compile_Time_Warning (Standard.True, "sendLimitedCastMessage unimplemented");
   end sendLimitedCastMessage;

   --------------------------
   -- sendBroadcastMessage --
   --------------------------

   procedure sendBroadcastMessage
     (This : in out Route_Aggregator_Mailbox;
      Msg  : Message_Root'Class)
   is
   begin
      pragma Compile_Time_Warning (Standard.True, "sendBroadcastMessage unimplemented");
   end sendBroadcastMessage;

end Route_Aggregator_Communication;

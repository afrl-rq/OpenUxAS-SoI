with Route_Aggregator_Messages; use Route_Aggregator_Messages;

--  Package only concerned with message passing. It defines its own state,
--  named Mailbox here, which is not mixed with the state of the service.

package Route_Aggregator_Communication with SPARK_Mode is

   type Route_Aggregator_Mailbox is limited private;

   type MessageGroup is (GroundPathPlanner, AircraftPathPlanner);

   procedure sendLimitedCastMessage
     (This : in out Route_Aggregator_Mailbox;
      Group : MessageGroup;
      Msg   : Message_Root'Class);

   procedure sendBroadcastMessage
     (This : in out Route_Aggregator_Mailbox;
      Msg   : Message_Root'Class);

private
   pragma SPARK_Mode (Off);
   type  Route_Aggregator_Mailbox is tagged null record;
end Route_Aggregator_Communication;

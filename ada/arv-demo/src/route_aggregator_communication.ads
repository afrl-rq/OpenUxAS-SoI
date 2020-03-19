with Route_Aggregator_Messages; use Route_Aggregator_Messages;
with Route_Aggregator_Common;   use Route_Aggregator_Common;

private with Ada.Strings.Unbounded;
private with UxAS.Comms.LMCP_Object_Message_Sender_Pipes;

--  Package only concerned with message passing. It defines its own state,
--  named Mailbox here, which is not mixed with the state of the service.

package Route_Aggregator_Communication with SPARK_Mode is

   type Route_Aggregator_Mailbox is limited private;

   type MessageGroup is (GroundPathPlanner, AircraftPathPlanner);

   procedure Initialize
     (This         : out Route_Aggregator_Mailbox;
      Source_Group : String;
      Unique_Id    : Int64;
      Entity_Id    : UInt32;
      Service_Id   : UInt32);

   procedure sendLimitedCastMessage
     (This : in out Route_Aggregator_Mailbox;
      Group : MessageGroup;
      Msg   : Message_Root'Class);

   procedure sendBroadcastMessage
     (This : in out Route_Aggregator_Mailbox;
      Msg   : Message_Root'Class);

   procedure Get_Next_Unique_Sending_Message_Id
     (This  : in out Route_Aggregator_Mailbox;
      Value : out Int64);

private
   pragma SPARK_Mode (Off);

   use Ada.Strings.Unbounded;

   use UxAS.Comms.LMCP_Object_Message_Sender_Pipes;

   type  Route_Aggregator_Mailbox is tagged limited record
      Message_Sender_Pipe           : LMCP_Object_Message_Sender_Pipe;
      Source_Group                  : Unbounded_String;
      Unique_Entity_Send_Message_Id : Int64;
   end record;

end Route_Aggregator_Communication;

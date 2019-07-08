--  see OpenUxAS\src\Communications\ZeroMqAddressedAttributedMessageReceiver.h

with UxAS.Comms.Data.Addressed.Attributed;  use  UxAS.Comms.Data.Addressed.Attributed;
with UxAS.Common.Sentinel_Serial_Buffers;   use UxAS.Common.Sentinel_Serial_Buffers;

with Ada.Containers.Formal_Doubly_Linked_Lists;

package UxAS.Comms.Transport.Receiver.ZeroMQ.Addr_Attr_Msg_Receivers is

   type ZeroMq_Addressed_Attributed_Message_Receiver is
     new ZeroMq_Receiver_Base with private;
   --  Receives ZeroMQ transported messages and converts them into an
   --  Addressed_Attributed_Message data object

   type ZeroMq_Addressed_Attributed_Message_Receiver_Ref is access all ZeroMq_Addressed_Attributed_Message_Receiver;

   type Any_ZeroMq_Addressed_Attributed_Message_Receiver is access all ZeroMq_Addressed_Attributed_Message_Receiver'Class;

   overriding
   procedure Initialize
     (This                 : in out ZeroMq_Addressed_Attributed_Message_Receiver;
      Entity_Id            : UInt32;
      Service_Id           : UInt32;
      Socket_Configuration : ZeroMq_Socket_Configuration);

   procedure Get_Next_Message
     (This : in out ZeroMq_Addressed_Attributed_Message_Receiver;
      Msg  : out Addressed_Attributed_Message_Ref);

   Max_Message_Deque_Depth : constant := 255; -- arbitrary

private

   package Message_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type => Addressed_Attributed_Message_Ref);

   subtype Message_Ptr_Deque is Message_Lists.List (Capacity => Max_Message_Deque_Depth);

   type ZeroMq_Addressed_Attributed_Message_Receiver is new ZeroMq_Receiver_Base with record
      Is_Tcp_Stream           : Boolean;
      Receive_Tcp_Data_Buffer : Sentinel_Serial_Buffer (Capacity => Sentinal_Buffer_Max_Capacity);
      Received_Messages       : Message_Ptr_Deque;
   end record;

end UxAS.Comms.Transport.Receiver.ZeroMQ.Addr_Attr_Msg_Receivers;

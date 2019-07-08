with ZMQ.Sockets;
with ZMQ.Contexts;
with ZMQ.Messages;
with Ada.Text_IO;            use Ada.Text_IO;
with AVTAS.LMCP.Types;       use AVTAS.LMCP.Types;
with AVTAS.LMCP.ByteBuffers; use AVTAS.LMCP.ByteBuffers;

with Avtas.Lmcp.Factory;

procedure Test_Msg_Decode is
   Ctx : ZMQ.Contexts.Context;
   Sub : ZMQ.Sockets.Socket;
   Buffer : ByteBuffer (Capacity => 4*1024);
begin
   Ctx.Set_Number_Of_IO_Threads (1);

   Sub.Initialize (Ctx, ZMQ.Sockets.SUB);

   Sub.Connect ("tcp://127.0.0.1:5560");

   -- Accept all forwarded messages (filtering on PUB side via 'SubscribeToMessage' child elements)
   Sub.Establish_Message_Filter ("");

   loop
      declare
         ZmqMsg : ZMQ.Messages.Message;
      begin
         ZmqMsg.Initialize (0);
         Buffer.Clear;

         Sub.Recv (ZmqMsg);
--           Put_Line (ZmqMsg.GetData);

         Buffer.Put_Raw_Bytes (ZmqMsg.GetData);
         Buffer.Rewind;
         declare
            CtrlStr   : Int32;
            MsgSize   : UInt32;
            MsgExists : Boolean;
            SeriesId  : Int64;
            MsgType   : Uint32;
            Version   : Uint16;

            LMCP_CONTROL_STR : constant Int32  := 1634103916;
         begin
            Buffer.Get_Int32 (CtrlStr);
            if CtrlStr /= LMCP_CONTROL_STR then
               Put_Line ("wrong LMCP_CONTROL_STR:" & CtrlStr'Image);
               goto Continue;
            end if;
            Buffer.Get_UInt32 (MsgSize);
            if Buffer.Capacity < MsgSize then
               Put_Line ("wrong msgsize:" & MsgSize'Image);
               goto Continue;
            end if;
            if not avtas.lmcp.factory.Validate (Buffer) then
               Put_Line ("checksum not valid");
               goto Continue;
            end if;
            Buffer.Get_Boolean (MsgExists);
            if not MsgExists then
               Put_Line ("msg not present");
               goto Continue;
            end if;

            Buffer.Get_Int64 (SeriesId);
            Buffer.Get_UInt32 (MsgType);
            Buffer.Get_UInt16 (Version);

            Put_Line ("SeriesId:" & SeriesId'Image);
            Put_Line ("MsgType:" & MsgType'Image);
            Put_Line ("Version:" & Version'Image);
         end;
      end;
      <<Continue>>
   end loop;
end Test_Msg_Decode;

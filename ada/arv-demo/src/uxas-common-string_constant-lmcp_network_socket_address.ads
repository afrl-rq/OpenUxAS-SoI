--  see OpenUxAS\src\Includes\Constants\UxAS_String.h

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

package UxAS.Common.String_Constant.Lmcp_Network_Socket_Address is

   --  NOTE: we are modifying the actual socket addresses used in the full C++
   --  version so that the Ada demo, running as a separate process, can listen
   --  for the required LMCP messages. Therefore, since it is a separate
   --  process, we don't use the "inproc" addresses. Instead we use the
   --  addresses used by the LmcpObjectNetworkPublishPullBridge bridge, which
   --  are specified in the XML configuration files. We want to retain use of
   --  this package spec though, so we change the two necessary declarations
   --  so that they are not constant, and for the sake of easily changing them
   --  at run-time (from the XML file), we use Unbounded_String. In a full Ada
   --  version of UxAs, with everything in the same process, we would not need
   --  these changes because the "inproc" addresses would be appropriate.

   InProc_ThreadControl        : constant String := "inproc://thread_control";
   InProc_From_MessageHub      : Unbounded_String := To_Unbounded_String ("inproc://from_message_hub");   -- "tcp://127.0.0.1:5560" -- the Pub address
   InProc_To_MessageHub        : Unbounded_String := To_Unbounded_String ("inproc://to_message_hub");     -- "tcp://127.0.0.1:5561" -- the Pull address
   InProc_ConfigurationHub     : constant String := "inproc://configuration_hub";
   InProc_ManagerThreadControl : constant String := "inproc://manager_thread_control";

end UxAS.Common.String_Constant.Lmcp_Network_Socket_Address;

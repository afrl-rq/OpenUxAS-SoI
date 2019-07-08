--  see OpenUxAS\src\Includes\Constants\UxAS_String.h

package UxAS.Common.String_Constant.Lmcp_Network_Socket_Address is

   InProc_ThreadControl        : constant String := "inproc://thread_control";
   InProc_From_MessageHub      : constant String := "tcp://127.0.0.1:5560";    --  "inproc://from_message_hub";
   InProc_To_MessageHub        : constant String := "tcp://127.0.0.1:5561";    --  "inproc://to_message_hub";
   InProc_ConfigurationHub     : constant String := "inproc://configuration_hub";
   InProc_ManagerThreadControl : constant String := "inproc://manager_thread_control";

end UxAS.Common.String_Constant.Lmcp_Network_Socket_Address;

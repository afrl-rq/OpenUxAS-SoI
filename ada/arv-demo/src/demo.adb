with Ada.Text_IO;    use Ada.Text_IO;
with Ada.Exceptions; use Ada.Exceptions;
with DOM.Core;       use DOM.Core;
with DOM.Core.Nodes; use DOM.Core.Nodes;
with DOM.Core.Elements;

with Ctrl_C_Handler;

with UxAS.Common.Configuration_Manager;   use UxAS.Common;
with UxAS.Comms.LMCP_Net_Client.Service;  use UxAS.Comms.LMCP_Net_Client.Service;

with UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation;
pragma Unreferenced (UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation);
--  need package in closure for sake of package executable part

with UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation;
pragma Unreferenced (UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation);
--  need package in closure for sake of package executable part

with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with UxAS.Common.String_Constant.Lmcp_Network_Socket_Address;

procedure Demo is
   Successful  : Boolean;
   New_Service : Any_Service;

   XML_Cfg_File_Name : constant String := "./cfg.xml";

   All_Enabled_Services : DOM.Core.Element;
   All_Enabled_Bridges  : DOM.Core.Element;

   From_Msg_Hub, To_Msg_Hub : Unbounded_String;
   --  These are the TCP address we use for this separate Ada process
   --  to communicate with the UxAS process in C++, taken from the
   --  LmcpObjectNetworkPublishPullBridge arguments in the XML file.

   procedure Launch_Services (Services : DOM.Core.Element; Successful : out Boolean);
   --  Instantiate, configure, initialize, and start each service specified in
   --  the configuration XML file. This is what ServiceManager::createService()
   --  would do, if implemented.

   procedure Get_LMCP_Socket_Addresses
     (Bridges      : DOM.Core.Element;
      Pub_Address  : out Unbounded_String;
      Pull_Address : out Unbounded_String);
   --  Find the LmcpObjectNetworkPublishPullBridge specification in the
   --  configuration XML file and get the corresponding the TCP addresses to
   --  use in package UxAS.Common.String_Constant.Lmcp_Network_Socket_Address.

   ---------------------
   -- Launch_Services --
   ---------------------

   procedure Launch_Services (Services : DOM.Core.Element; Successful : out Boolean) is
      Next : DOM.Core.Node;
   begin
      Next := First_Child (Services);
      while Next /= null loop
         declare
            Service_Type_Name : constant String := DOM.Core.Elements.Get_Attribute (Next, Name => "Type");
         begin
            New_Service := Instantiate_Service (Service_Type_Name);
            if New_Service = null then
               Put_Line ("Could not Instantiate_Service for " & Service_Type_Name);
               Successful := False;
               return;
            end if;

            New_Service.Configure_Service
              (Parent_Of_Work_Directory => Configuration_Manager.Root_Data_Work_Directory,
               Service_XML_Node         => Next,
               Result                   => Successful);
            if not Successful then
               Put_Line ("Could not Configure_Service for " & Service_Type_Name);
               return;
            end if;

            New_Service.Initialize_And_Start (Successful);
            if not Successful then
               Put_Line ("Could not Initialize_And_Start " & Service_Type_Name);
               return;
            end if;

            Put_Line ("Successfully launched " & Service_Type_Name);
            Next := Next_Sibling (Next);
         end;
      end loop;
   end Launch_Services;

   -------------------------------
   -- Get_LMCP_Socket_Addresses --
   -------------------------------

   procedure Get_LMCP_Socket_Addresses
     (Bridges      : DOM.Core.Element;
      Pub_Address  : out Unbounded_String;
      Pull_Address : out Unbounded_String)
   is
      Next : DOM.Core.Node;
   begin
      Pub_Address := Null_Unbounded_String;
      Pull_Address := Null_Unbounded_String;

      --  <Bridge Type="LmcpObjectNetworkPublishPullBridge" AddressPUB="tcp://127.0.0.1:5560" AddressPULL="tcp://127.0.0.1:5561">
      Next := First_Child (Bridges);
      while Next /= null loop
         declare
            Service_Type_Name : constant String := DOM.Core.Elements.Get_Attribute (Next, Name => "Type");
         begin
            if Service_Type_Name = "LmcpObjectNetworkPublishPullBridge" then
               Pub_Address  := To_Unbounded_String (DOM.Core.Elements.Get_Attribute (Next, Name => "AddressPUB"));
               Pull_Address := To_Unbounded_String (DOM.Core.Elements.Get_Attribute (Next, Name => "AddressPULL"));
               Put_Line ("Found bridge addressPUB:  """ & To_String (Pub_Address) & '"');
               Put_Line ("Found bridge addressPULL: """ & To_String (Pull_Address) & '"');
               return;
            end if;
            Next := Next_Sibling (Next);
         end;
      end loop;
   end Get_LMCP_Socket_Addresses;

begin
   Ctrl_C_Handler;

   Configuration_Manager.Instance.Load_Base_XML_File (XML_Cfg_File_Name, Successful);
   if not Successful then
      Put_Line ("Could not load base XML file '" & XML_Cfg_File_Name & "'");
      return;
   end if;

   --  First, search All_Enabled_Bridges for the TCP addresses to use, rather than hard-coding them in
   --  package UxAS.Common.String_Constant.Lmcp_Network_Socket_Address
   --
   --  NOTE: We MUST do this before we launch the services since they will use the addresses in that package...

   Configuration_Manager.Instance.Get_Enabled_Bridges (All_Enabled_Bridges, Successful);
   if not Successful then
      Put_Line ("Could not Get_Enabled_Bridges via config manager");
      return;
   end if;

   Get_LMCP_Socket_Addresses (All_Enabled_Bridges, Pub_Address => From_Msg_Hub, Pull_Address => To_Msg_Hub);
   if From_Msg_Hub = Null_Unbounded_String or To_Msg_Hub = Null_Unbounded_String then
      Put_Line ("Could not get bridge's two TCP addresses from XML file");
      return;
   end if;

   UxAS.Common.String_Constant.Lmcp_Network_Socket_Address.InProc_From_MessageHub := From_Msg_Hub;
   UxAS.Common.String_Constant.Lmcp_Network_Socket_Address.InProc_To_MessageHub := To_Msg_Hub;

   --  Now launch the services specified in the config XML file

   Configuration_Manager.Instance.Get_Enabled_Services (All_Enabled_Services, Successful);
   if not Successful then
      Put_Line ("Could not Get_Enabled_Services via config manager");
      return;
   end if;

   Launch_Services (All_Enabled_Services, Successful);
   if not Successful then
      return;
   end if;

   Put_Line ("Initialization complete");
exception
   when Error : others =>
      Put_Line (Exception_Information (Error));
end Demo;

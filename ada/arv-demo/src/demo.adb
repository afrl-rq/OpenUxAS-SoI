with Ada.Text_IO;    use Ada.Text_IO;
with Ada.Exceptions; use Ada.Exceptions;

with UxAS.Common.Configuration_Manager;  use UxAS.Common;

with UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation;
pragma Unreferenced (UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation);
--  need package in closure for sake of package executable part

with UxAS.Comms.LMCP_Net_Client.Service;  use UxAS.Comms.LMCP_Net_Client.Service;

with DOM.Core;

procedure Demo is
   Success   : Boolean;
   Validator : Any_Service;

   XML_Cfg_File_Name : constant String := "./cfg.xml";

   All_Enabled_Services : DOM.Core.Element;
begin
   Configuration_Manager.Instance.Load_Base_XML_File (XML_Cfg_File_Name, Success);
   if not Success then
      Put_Line ("Could not load base XML file '" & XML_Cfg_File_Name & "'");
      return;
   end if;

   Configuration_Manager.Instance.Get_Enabled_Services (All_Enabled_Services, Success);
   if not Success then
      Put_Line ("Could not Get_Enabled_Services from config manager");
      return;
   end if;

   --  see instantiateConfigureInitializeStartService() in ServiceManager for the following

   Validator := Instantiate_Service (Type_Name => "AutomationRequestValidatorService");

   Validator.Configure_Service
     (Parent_Of_Work_Directory => Configuration_Manager.Root_Data_Work_Directory,
      Service_XML_Node         => All_Enabled_Services,
      Result                   => Success);
   if not Success then
      Put_Line ("Could not Configure_Service for validator service");
      return;
   end if;

   Validator.Initialize_And_Start (Success);
   if not Success then
      Put_Line ("Could not Initialize_And_Start validator service");
      return;
   end if;

   Put_Line ("Initialization complete");
exception
   when Error : others =>
      Put_Line (Exception_Information (Error));
end Demo;

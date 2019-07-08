--  see OpenUxAS\src\Utilities\UxAS_ConfigurationManager.h

with DOM.Core;
with AVTAS.LMCP.Types;  use AVTAS.LMCP.Types;
with UxAS.Comms;

with Dynamic_Strings; use Dynamic_Strings;

package UxAS.Common.Configuration_Manager is

   type Manager (<>) is tagged limited private;

   type Any_Manager is access all Manager'Class;

   type Manager_Reference is access all Manager;

   function Instance return not null Manager_Reference;

   --  loadBaseXmlFile(const std::string& xmlFilePath = "./cfg/cfgbase.xml");
   procedure Load_Base_XML_File
     (This          : not null access Manager;
      XML_File_Path : String;
      Result        : out Boolean);

   --  loadBaseXmlString(const std::string& xmlString);
   procedure Load_Base_XML_String
     (This        : not null access Manager;
      XML_Content : String;
      Result      : out Boolean);

   --  unloads base configuration
   procedure Unload_XML (This : not null access Manager);

   function Get_Entity_Id (This : not null access Manager) return UInt32;

   function Get_Entity_Type (This : not null access Manager) return String;

   --  UxAS component-specific data directory name as a sub-directory of
   --  the application root data directory. TODO - assure uniqueness.
   --  getComponentDataDirectory(const std::string& directoryName)
   function Component_Data_Directory (Directory_Name : String) return String;

   --  true if using Zero MQ multi-part messaging; false if using Zero MQ
   --  single-part messaging
   Is_ZeroMq_Multipart_Message : constant Boolean := False;

   --  UxAS application root work directory that hosts
   --  sub-directories containing in-work and/or output files created by
   --  components (e.g., services). For the case of reading data, components
   --  should read data from a <i>data</i> directory - see getRootDataInDirectory
   --  method.
   function Root_Data_Work_Directory return String;  --  "./datawork/";

   Root_Work_Dir_Capacity : constant := 255; -- arbitrary

   --  the static variable is just public in the C++ code so we provide a getter/setter
   procedure Set_Root_Data_Work_Directory (Value : String) with
     Pre => Value'Length <= Root_Work_Dir_Capacity;

   --  UxAS application root data directory that hosts sub-directories
   --  containing input data for components (e.g., services). Components
   --  should only read data from these sub-directories . In-work and
   --  output data should be written to a <i>work</i> directory - see
   --  getRootDataWorkDirectory method.
   function Root_DataIn_Directory return String is
     ("./datain/");

   --  UxAS application root work directory that hosts sub-directories
   --  containing in-work and/or output files created by components (e.g.,
   --  services). For the case of reading data, components should read data
   --  from a <i>data</i> directory - see getRootDataInDirectory method.
   function Root_DataRef_Directory return String is
     ("./dataref/");

   --  Returns service configurations for services to be enabled at entity
   --  startup. The configurations are resolved from base XML.
   procedure Get_Enabled_Services
     (This     : not null access Manager;
      Services : out DOM.Core.Element;
      Result   : out Boolean);

   --  Returns bridge configurations for bridges to be enabled at entity
   --  startup. The configurations are resolved from base XML.
   procedure Get_Enabled_Bridges
     (This    : not null access Manager;
      Bridges : out DOM.Core.Element;
      Result  : out Boolean);

private

   Root_Data_Work_Dir : Dynamic_String := Instance (Root_Work_Dir_Capacity, Content => "./datawork/");

   use UxAS.Comms;

   type Manager is tagged limited
      record
         Entity_Id                      : UInt32 := 0;  -- default is 0 but also set indirectly via Load_XML
         Entity_Type                    : Dynamic_String (Capacity => Entity_Type_Max_Length); -- default is "" but also set indirectly via Load_XML
         Enabled_Bridges_XML_Doc_Built  : Boolean := False;
         Enabled_Bridges_XML_Doc        : DOM.Core.Document;
         Enabled_Services_XML_Doc_Built : Boolean := False;
         Enabled_Services_XML_Doc       : DOM.Core.Document;
         Base_XML_Doc_Loaded            : Boolean := False;
         Base_XML_Doc                   : DOM.Core.Document;
      end record;

   The_Instance : Manager_Reference;
   --  we use lazy allocation...

   procedure Load_XML
     (This        : not null access Manager;
      XML_Input   : String;
      XML_Is_File : Boolean;
      Is_Base_XML : Boolean;
      Result      : out Boolean);

   procedure Set_Entity_Values_From_XML_Node
     (This   : not null access Manager;
      Root   : DOM.Core.Document;
      Result : out Boolean);

   --  Populate the specified XML document Doc Doc with all elements in the
   --  base XML doc that have names matching Node_Name
   --
   --  populateEnabledComponentXmlNode(pugi::xml_node& uxasNode, const std::string& nodeName)
   procedure Populate_Enabled_Components
     (This      : not null access Manager;
      Doc       : in out DOM.Core.Document;
      Node_Name : String);

   --  implement the routine from the PUGI XML library
   procedure Reset (This : in out DOM.Core.Document);

end UxAS.Common.Configuration_Manager;

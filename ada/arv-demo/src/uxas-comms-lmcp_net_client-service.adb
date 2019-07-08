with Ada.Containers.Formal_Hashed_Maps;
with Ada.Strings.Hash;
with Ada.Directories;

with DOM.Core.Documents;
with DOM.Core.Elements;
with Input_Sources.Strings;
with DOM.Readers;
with Sax.Encodings;

with UxAS.Common.String_Constant;

package body UxAS.Comms.LMCP_Net_Client.Service is

   function Hashed_Service_Type_Name (Element : Service_Type_Name) return Ada.Containers.Hash_Type is
      (Ada.Strings.Hash (Value (Element)));

   package Creation_Function_To_Service_Names is new Ada.Containers.Formal_Hashed_Maps
     (Element_Type    => Service_Creation_Function_Pointer,
      Key_Type        => Service_Type_Name,
      Hash            => Hashed_Service_Type_Name,
      Equivalent_Keys => "=");

   Function_Map_Capacity : constant := 100; -- arbitrary

   subtype Creation_Function_Map is Creation_Function_To_Service_Names.Map
     (Function_Map_Capacity,
      Creation_Function_To_Service_Names.Default_Modulus (Function_Map_Capacity));

   --------------------------------
   -- Creation_Function_Registry --
   --------------------------------

   --      static
   --      std::unordered_map<std::string, ServiceBase::serviceCreationFunctionPointer>&
   --      createFunctionByServiceType()

   --  We implement createFunctionByServiceType via this simple decl
   Creation_Function_Registry : Creation_Function_Map;

   -------------------------------------------------
   -- Register_Service_Creation_Function_Pointers --
   -------------------------------------------------

   procedure Register_Service_Creation_Function_Pointers
     (Service_Type_Names : Service_Type_Names_List;
      Associated_Creator : Service_Creation_Function_Pointer)
   is
      use Creation_Function_To_Service_Names;
      C : Cursor;
   begin
      for Name of Service_Type_Names loop
         C := Find (Creation_Function_Registry, Name);
         if C = No_Element then
            Insert (Creation_Function_Registry, Name, Associated_Creator);
         else
            --  note that the C++ version issues a warning here
            Replace_Element (Creation_Function_Registry, C, Associated_Creator);
         end if;
      end loop;
   end Register_Service_Creation_Function_Pointers;

   -----------------------
   -- Construct_Service --
   -----------------------

   procedure Construct_Service
     (This                : in out Service_Base;
      Service_Type        : String;
      Work_Directory_Name : String)
   is
   begin
      This.Construct_Client;

      --     ServiceBase::ServiceBase(const std::string& serviceType, const std::string& workDirectoryName)
      --      : m_serviceType(serviceType), m_workDirectoryName(workDirectoryName)
      --      {
      --          m_serviceId = m_networkId;
      Copy (Service_Type, This.Service_Type);
      Copy (Work_Directory_Name, This.Work_Directory_Name);
      This.Service_Id := UInt32'Mod (This.Network_Id);

      This.Is_Constructed := True;
   end Construct_Service;

   -------------------------
   -- Instantiate_Service --
   -------------------------

   function Instantiate_Service
     (Type_Name : String)
      return Any_Service
   is
      Result  : Any_Service;
      Target  : constant Service_Type_Name := Instance (Service_Type_Name_Max_Length, Type_Name);
      Creator : Service_Creation_Function_Pointer;

      use Creation_Function_To_Service_Names;
      C : Cursor;
   begin
      --      static
      --      std::unique_ptr<ServiceBase>
      --      instantiateService(const std::string& serviceType)
      --      {
      --          auto it = createFunctionByServiceType().find(serviceType);
      --          ServiceBase * newService(it == createFunctionByServiceType().end() ? nullptr : (it->second)());
      --          std::unique_ptr<ServiceBase> service(newService);
      --          return (service);
      --      };
      C := Find (Creation_Function_Registry, Target);
      if C = No_Element then
         return null;
      end if;
      Creator := Element (Creation_Function_Registry, C);  -- get the creator function
      Result := Creator.all;  -- call the function
      return Result;
   end Instantiate_Service;

   -----------------------
   -- Configure_Service --
   -----------------------

   procedure Configure_Service
     (This                     : in out Service_Base;
      Parent_Of_Work_Directory : String;
      ServiceXml               : String;
      Result                   : out Boolean)
   is
      use DOM.Core;
      use DOM.Readers;
      use Input_Sources.Strings;

      Input  : String_Input;
      Reader : Tree_Reader;
      Doc    : Document;
   begin
      Input_Sources.Strings.Open (ServiceXml, Sax.Encodings.Encoding, Input);
      Reader.Parse (Input);
      Close (Input);
      Doc := Get_Tree (Reader);

      Configure_Service
        (This,
         Parent_Of_Work_Directory,
         Documents.Get_Element (Doc),
         This.Is_Configured);

      Result := This.Is_Configured;
   end Configure_Service;

   -----------------------
   -- Configure_Service --
   -----------------------

   procedure Configure_Service
     (This                     : in out Service_Base;
      Parent_Of_Work_Directory : String;
      Service_Xml_Node         : DOM.Core.Element;
      Result                   : out Boolean)
   is

      function Slash_Appended (S : String) return String with
        Pre  => S'Length > 0,
        Post => Slash_Appended'Result (Slash_Appended'Result'Last) = '/';

      function Slash_Appended (S : String) return String is
         (if S (S'Last) = '/' then S else S & '/');

   begin
      if This.Work_Directory_Name /= "" then
         Copy (Slash_Appended (Parent_Of_Work_Directory) & Slash_Appended (Value (This.Work_Directory_Name)),
               To => This.Work_Directory_Path);
      else
         Clear (This.Work_Directory_Path);
      end if;

      Configure_Network_Client
        (This,
         Subclass_Type_Name      => Value (This.Service_Type),
         Processing_Kind         => This.Processing_Type,
         Network_Client_XML_Node => Service_Xml_Node,
         Result                  => Result);

      if Result then
         declare
            Group : constant DOM.Core.DOM_String := DOM.Core.Elements.Get_Attribute (Service_Xml_Node, Name => UxAS.Common.String_Constant.MessageGroup);
         begin
            if Group /= "" then
               --  set source group value that will be assigned to source group field of sent messages
               Copy (Group, To => This.Message_Source_Group);

               --  subscribe to messages addressed to non-empty source group value
               This.Add_Subscription_Address (Group, Success => Result);
            end if;
         end;
      end if;

      This.Is_Configured := Result;
   end Configure_Service;

   ----------------------------------
   -- Initialize_And_Start_Service --
   ----------------------------------

   procedure Initialize_And_Start_Service
     (This   : in out Service_Base;
      Result : out Boolean)
   is
   begin
      Result := False;
      if This.Is_Configured then
         if not Empty (This.Work_Directory_Path) then
            begin
               Ada.Directories.Create_Path (Value (This.Work_Directory_Path));
            exception  --  TODO !!!!!
               when others =>
                  return;
            end;
         end if;
         Initialize_And_Start (This, Result);
      end if;
   end Initialize_And_Start_Service;

   ---------------------------
   -- Get_Unique_Service_Id --
   ---------------------------

   function Get_Unique_Service_Id return Int64 is
      Result : Int64;
   begin
      Get_Unique_Network_Client_Id (Result);
      return Result;
   end Get_Unique_Service_Id;

   --------------------
   -- Get_Service_Id --
   --------------------

   function Get_Service_Id (This : Service_Base) return UInt32 is
     (This.Service_Id);

   ----------------------
   -- Get_Service_Type --
   ----------------------

   function Get_Service_Type (This : Service_Base) return String is
      (Value (This.Service_Type));

   -----------------------------
   -- Get_Work_Directory_Name --
   -----------------------------

   function Get_Work_Directory_Name (This : Service_Base) return String is
     (Value (This.Work_Directory_Name));

   ----------------
   -- Configured --
   ----------------

   function Configured (This : Service_Base) return Boolean is
     (This.Is_Configured);

   -----------------
   -- Constructed --
   -----------------

   function Constructed (This : Service_Base) return Boolean is
      (This.Is_Constructed);

end UxAS.Comms.LMCP_Net_Client.Service;

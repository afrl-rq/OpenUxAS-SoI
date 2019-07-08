--  see C:\AFRL_mentorship\OpenUxAS\src\Utilities\UxAS_ConfigurationManager.cpp

with String_Utils;  use String_Utils;
with Ada.Strings.Fixed;

with Input_Sources.Strings;
with Input_Sources.File;
with DOM.Readers;
with DOM.Core.Documents;
with DOM.Core.Nodes;
with Sax.Encodings;
with DOM.Core.Elements;

with UxAS.Common.String_Constant;

package body UxAS.Common.Configuration_Manager is

   --------------
   -- Instance --
   --------------

   function Instance return not null Manager_Reference is
   begin
      if The_Instance = null then
         The_Instance := new Manager;
      end if;
      return The_Instance;
   end Instance;

   -------------------
   -- Get_Entity_Id --
   -------------------

   function Get_Entity_Id (This : not null access Manager) return UInt32 is
      (This.Entity_Id);

   ---------------------
   -- Get_Entity_Type --
   ---------------------

   function Get_Entity_Type (This : not null access Manager) return String is
     (Value (This.Entity_Type));

   --------------------------
   -- Get_Enabled_Services --
   --------------------------

   procedure Get_Enabled_Services
     (This     : not null access Manager;
      Services : out DOM.Core.Element;
      Result   : out Boolean)
   is
   begin
      if This.Base_XML_Doc_Loaded and not This.Enabled_Services_XML_Doc_Built then
         Reset (This.Enabled_Services_XML_Doc);
         This.Populate_Enabled_Components (This.Enabled_Services_XML_Doc, Node_Name => String_Constant.Service);
         This.Enabled_Services_XML_Doc_Built := True;
      end if;
      Services := DOM.Core.Documents.Get_Element (This.Enabled_Services_XML_Doc);
      Result := True;
   exception
      when others =>
         Result := False;
   end Get_Enabled_Services;

   -------------------------
   -- Get_Enabled_Bridges --
   -------------------------

   procedure Get_Enabled_Bridges
     (This    : not null access Manager;
      Bridges : out DOM.Core.Element;
      Result  : out Boolean)
   is
   begin
      if This.Base_XML_Doc_Loaded and not This.Enabled_Bridges_XML_Doc_Built then
         Reset (This.Enabled_Bridges_XML_Doc);
         This.Populate_Enabled_Components (This.Enabled_Bridges_XML_Doc, Node_Name => String_Constant.Bridge);
         This.Enabled_Bridges_XML_Doc_Built := True;
      end if;
      Bridges := DOM.Core.Documents.Get_Element (This.Enabled_Bridges_XML_Doc);
      Result := True;
   exception
      when others =>
         Result := False;
   end Get_Enabled_Bridges;

   ---------------------------------
   -- Populate_Enabled_Components --
   ---------------------------------

   procedure Populate_Enabled_Components
     (This      : not null access Manager;
      Doc       : in out DOM.Core.Document;
      Node_Name : String)
   is
      use DOM.Core;
      use DOM.Core.Nodes;

      Unused            : DOM.Core.Element;
      Matching_Children : Node_List := DOM.Core.Documents.Get_Elements_By_Tag_Name (This.Base_XML_Doc, Node_Name);
      UxAS_Node         : DOM.Core.Element;
   begin
      UxAS_Node := DOM.Core.Documents.Create_Element (Doc, Tag_Name => String_Constant.UxAS);
      UxAS_Node := DOM.Core.Nodes.Append_Child (Doc, New_Child => UxAS_Node);

      DOM.Core.Elements.Set_Attribute (UxAS_Node, Name => "FormatVersion",            Value => "1.0");
      DOM.Core.Elements.Set_Attribute (UxAS_Node, Name => String_Constant.EntityId,   Value => To_String (This.Get_Entity_Id));
      DOM.Core.Elements.Set_Attribute (UxAS_Node, Name => String_Constant.EntityType, Value => This.Get_Entity_Type);

      for K in Natural range 1 .. DOM.Core.Nodes.Length (Matching_Children) loop
         Unused := Append_Child
           (UXAS_Node,
            New_Child => DOM.Core.Documents.Import_Node (Doc, Item (Matching_Children, K-1), Deep => True));
      end loop;
      DOM.Core.Free (Matching_Children);
   end Populate_Enabled_Components;

   ------------------------
   -- Load_Base_XML_File --
   ------------------------

   procedure Load_Base_XML_File
     (This          : not null access Manager;
      XML_File_Path : String;
      Result        : out Boolean)
   is
   begin
      This.Load_XML
        (XML_Input   => XML_File_Path,
         XML_Is_File => True,
         Is_Base_XML => True,
         Result      => Result);
   end Load_Base_XML_File;

   --------------------------
   -- Load_Base_XML_String --
   --------------------------

   procedure Load_Base_XML_String
     (This        : not null access Manager;
      XML_Content : String;
      Result      : out Boolean)
   is
   begin
      This.Load_XML
        (XML_Input   => XML_Content,
         XML_Is_File => False,
         Is_Base_XML => True,
         Result      => Result);
   end Load_Base_XML_String;

   --------------
   -- Load_XML --
   --------------

   procedure Load_XML
     (This        : not null access Manager;
      XML_Input   : String;
      XML_Is_File : Boolean;
      Is_Base_XML : Boolean;
      Result      : out Boolean)
   is
      XML_Parse_Success : Boolean;
      Reader : DOM.Readers.Tree_Reader;
   begin
      if Is_Base_XML then
         if This.Base_XML_Doc_Loaded then
            Reset (This.Base_XML_Doc);
            This.Base_XML_Doc_Loaded := False;
            This.Enabled_Bridges_XML_Doc_Built := False;
            This.Enabled_Services_XML_Doc_Built := False;
         end if;
         if XML_Is_File then
            declare
               Input : Input_Sources.File.File_Input;
            begin
               Input_Sources.File.Open (XML_Input, Input);
               Reader.Parse (Input);
               Input_Sources.File.Close (Input);
               This.Base_XML_Doc := DOM.Readers.Get_Tree (Reader);
               XML_Parse_Success := True;
            exception
               when others =>
                  XML_Parse_Success := False;
            end;
         else  --  input is not a file
            declare
               Input : Input_Sources.Strings.String_Input;
            begin
               Input_Sources.Strings.Open (XML_Input, Sax.Encodings.Encoding, Input);
               Reader.Parse (Input);
               Input_Sources.Strings.Close (Input);
               This.Base_XML_Doc := DOM.Readers.Get_Tree (Reader);
               XML_Parse_Success := True;
            exception
               when others =>
                  XML_Parse_Success := False;
            end;
         end if;
         This.Base_XML_Doc_Loaded := True;
      end if;

      if XML_Parse_Success then
         This.Set_Entity_Values_From_XML_Node
           (Root   => This.Base_XML_Doc,
            Result => Result);
      end if;

      if not Result then
         if Is_Base_XML then
            This.Base_XML_Doc_Loaded := False;
         end if;
      end if;
   end Load_XML;

   ----------------
   -- Unload_XML --
   ----------------

   procedure Unload_XML (This : not null access Manager) is
   begin
      Reset (This.Base_XML_Doc);
      This.Base_XML_Doc_Loaded := False;
      Reset (This.Enabled_Bridges_XML_Doc);
      This.Enabled_Bridges_XML_Doc_Built := False;
      Reset (This.Enabled_Services_XML_Doc);
      This.Enabled_Services_XML_Doc_Built := False;
   end Unload_XML;

   -------------------------------------
   -- Set_Entity_Values_From_XML_Node --
   -------------------------------------

   procedure Set_Entity_Values_From_XML_Node
     (This   : not null access Manager;
      Root   : DOM.Core.Document;
      Result : out Boolean)
   is
      Success : Boolean := False;

      use DOM.Core;
      use DOM.Core.Elements;

      Children          : constant Node_List := DOM.Core.Documents.Get_Elements_By_Tag_Name (Root, String_Constant.UxAS);
      EntityInfoXmlNode : constant Node := DOM.Core.Nodes.Item (Children, Index => 0);
    begin
      if EntityInfoXmlNode /= null then
         declare
            Str : constant DOM_String := Get_Attribute (EntityInfoXmlNode, Name => String_Constant.EntityID);
         begin
            if Str /= "" then
               This.Entity_Id := UInt32'Value (Str);
               Success := True;
            end if;
         end;

         if Success then
            declare
               Str : constant DOM_String := Get_Attribute (EntityInfoXmlNode, Name => String_Constant.EntityType);
            begin
               if Str /= "" then
                  Copy (Str, To => This.Entity_Type);
               else
                  Success := False;
               end if;
            end;
         end if;

         --  and so on, for ConsoleLoggerSeverityLevel, MainFileLoggerSeverityLevel, etc.
         pragma Compile_Time_Warning (True, "Set_Entity_Values_From_XML_Node is incomplete");
      end if;

      Result := Success;
   end Set_Entity_Values_From_XML_Node;

   -----------
   -- Reset --
   -----------

   procedure Reset (This : in out DOM.Core.Document) is
      Impl : DOM.Core.DOM_Implementation;
   begin
      --  the Pugi version first does a destroy() call but that doesn't seem to
      --  exist in the XMLAda version
      This := DOM.Core.Create_Document (Impl);
   end Reset;

   ------------------------------
   -- Root_Data_Work_Directory --
   ------------------------------

   function Root_Data_Work_Directory return String is
      (Value (Root_Data_Work_Dir));

   ----------------------------------
   -- Set_Root_Data_Work_Directory --
   ----------------------------------

   procedure Set_Root_Data_Work_Directory (Value : String) is
   begin
      Copy (Value, To => Root_Data_Work_Dir);
   end Set_Root_Data_Work_Directory;

   ------------------------------
   -- Component_Data_Directory --
   ------------------------------

   function Component_Data_Directory (Directory_Name : String) return String is
      use Ada.Strings.Fixed;
      use Ada.Strings;

      Trimmed_Dir : constant String := Trim (Directory_Name, Both);
      Suffix      : constant String := (if Index (Trimmed_Dir, "/", Going => Backward) = 1 then "" else "/");
   begin
      --  return (s_rootDataInDirectory + directoryName + ((*(directoryName.rbegin()) == '/') ? "" : "/"));
      return Root_DataIn_Directory & Trimmed_Dir & Suffix;
   end Component_Data_Directory;

end UxAS.Common.Configuration_Manager;

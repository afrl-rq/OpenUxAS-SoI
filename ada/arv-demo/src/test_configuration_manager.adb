with Ada.Text_IO;    use Ada.Text_IO;
with Ada.Exceptions; use Ada.Exceptions;

with UXAS.Common.Configuration_Manager;  use UXAS.Common.Configuration_Manager;

procedure Test_Configuration_Manager is
   Successfull_Load : Boolean;
begin
   Instance.Load_Base_XML_File
     (XML_File_Path => "./cfg_WaterwaySearch.xml",
      Result        => Successfull_Load);

   if Successfull_Load then
      Put_Line (Instance.Get_Entity_Id'Image);
      Put_Line (Instance.Get_Entity_Type);
   end if;

   Put_Line ("Done");
exception
   when Error : others =>
      Put_Line (Exception_Name (Error));
      Put_Line (Exception_Message (Error));
end Test_Configuration_Manager;


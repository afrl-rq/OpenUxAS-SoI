with Ada.Text_IO; use Ada.Text_IO;

with Common_Formal_Containers;  use Common_Formal_Containers;

procedure Test is
   S : Int64_Set;
   use Int64_Sets;
begin
   Put_Line ("Starting");
   Include (S, 1000);
   Put_Line ("Done");
end Test;

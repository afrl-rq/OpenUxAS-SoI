with GNAT.OS_Lib;
with GNAT.Ctrl_C;

procedure Ctrl_C_Handler is
   procedure Flush;
   pragma Import (C, Flush, "__gcov_flush");
   procedure SIGINT_Exit is
   begin
      Flush;
      GNAT.OS_Lib.OS_Exit (1);
   end SIGINT_Exit;
begin
   GNAT.Ctrl_C.Install_Handler (SIGINT_Exit'Unrestricted_Access);
end Ctrl_C_Handler;
